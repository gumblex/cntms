#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import io
import re
import time
import math
import json
import random
import sqlite3
import weakref
import warnings
import itertools
import collections
import configparser
import collections.abc
import concurrent.futures

import pycurl
import prcoords
import tornado.web
import tornado.gen
import tornado.locks
import tornado.ioloop
import tornado.httpclient
import tornado.curl_httpclient
from PIL import Image

try:
    import certifi
    CA_CERTS = certifi.where()
except ImportError:
    CA_CERTS = None

warnings.simplefilter("ignore")

# Earth mean radius
R_EARTH = 6371000
RES_3857 = 40075016.685578486153
ORIGIN_3857 = 20037508.342789243077

CONFIG_FILE = 'tmsapi.ini'
CONFIG = {}
APIS = None

HEADERS_WHITELIST = {
    'Accept-Encoding',
    'Upgrade-Insecure-Requests',
    'Dnt',
    'Cookie',
    'User-Agent',
    'Accept',
    'Accept-Language'
}
HTTP_CLIENT = tornado.curl_httpclient.CurlAsyncHTTPClient()

def prepare_curl_socks5(curl):
    curl.setopt(pycurl.PROXYTYPE, pycurl.PROXYTYPE_SOCKS5)

def from4326_to3857(lon, lat):
    x = math.radians(lon) * 6378137
    y = math.asinh(math.tan(math.radians(lat))) * 6378137
    return (x, y)

class DBTileCache(collections.abc.MutableMapping):

    def __init__(self, filename, maxsize, ttl):
        self.maxsize = maxsize
        self.ttl = ttl
        self.db = sqlite3.connect(filename, isolation_level=None)
        self.db.execute('PRAGMA journal_mode=WAL')
        self.db.execute('CREATE TABLE IF NOT EXISTS cache ('
            'key TEXT PRIMARY KEY,'
            'expire INTEGER,'
            'updated INTEGER,'
            'mime TEXT,'
            'img BLOB'
        ') WITHOUT ROWID')
        self.db.execute('CREATE TABLE IF NOT EXISTS metadata ('
            'key TEXT PRIMARY KEY,'
            'value TEXT'
        ') WITHOUT ROWID')

    def __contains__(self, key):
        r = self.db.execute(
            'SELECT 1 FROM cache WHERE key=? AND expire>=?', (key, time.time())
            ).fetchone()
        return bool(r)

    def __getitem__(self, key):
        r = self.db.execute(
            'SELECT img, mime FROM cache WHERE key=? AND expire>=?', (key, time.time())
            ).fetchone()
        if r:
            return r
        else:
            raise KeyError(key)

    def save(self, key, value, ttl=None):
        if ttl is None:
            ttl = self.ttl
        now = int(time.time())
        self.db.execute('REPLACE INTO cache VALUES (?,?,?,?,?)',
            (key, now+ttl, now, value[1], value[0]))
        self.expire()

    def set_meta(self, key, value):
        self.db.execute('REPLACE INTO metadata VALUES (?,?)',
            (key, json.dumps(value)))

    def get_meta(self, key):
        row = self.db.execute(
            'SELECT value FROM metadata WHERE key=?', (key,)).fetchone()
        if row is None:
            return None
        return json.loads(row[0])

    def __setitem__(self, key, value):
        self.save(key, value)

    def __delitem__(self, key):
        self.db.execute('DELETE FROM cache WHERE key=?', (key,))

    def __iter__(self):
        for row in self.db.execute('SELECT key FROM cache'):
            yield row[0]

    def __len__(self):
        r = self.db.execute(
            'SELECT count(*) FROM cache WHERE expire>=?', (time.time(),)).fetchone()
        return r[0]

    def expire(self, etime=None):
        """Remove expired items from the cache."""
        self.db.execute('DELETE FROM cache WHERE key NOT IN ('
            'SELECT key FROM cache WHERE expire>=? ORDER BY updated DESC LIMIT ?)',
            (etime or time.time(), self.maxsize))

    def clear(self):
        self.db.execute('DELETE FROM cache')

    def get(self, key, default=None):
        try:
            return self.__getitem__(key)
        except KeyError:
            return default

class MemoryTileCache(collections.abc.MutableMapping):

    def __init__(self, maxsize, ttl):
        self.maxsize = maxsize
        self.ttl = ttl
        self.cache = collections.OrderedDict()
        self.metadata = {}

    def __contains__(self, key):
        if key not in self.cache:
            return False
        return self.cache[key][0] >= time.time()

    def __getitem__(self, key):
        row = self.cache[key]
        if row[0] < time.time():
            del self.cache[key]
            raise KeyError(key)
        return row[1:]

    def save(self, key, value, ttl=None):
        if ttl is None:
            ttl = self.ttl
        now = int(time.time())
        self.cache[key] = (now+ttl, value[0], value[1])
        self.expire()

    def set_meta(self, key, value):
        self.metadata[key] = value

    def get_meta(self, key):
        return self.metadata.get(key)

    def __setitem__(self, key, value):
        self.save(key, value)

    def __delitem__(self, key):
        del self.cache[key]

    def __iter__(self):
        return iter(self.cache)

    def __len__(self):
        return len(self.cache)

    def expire(self, etime=None):
        """Remove expired items from the cache."""
        orig_len = len(self.cache)
        if orig_len < self.maxsize:
            return
        keys = tuple(self.cache.keys())
        i = 0
        now = time.time()
        while (i < orig_len and (
            self.cache[keys[i]][0] < now or len(self.cache) > self.maxsize
        )):
            self.cache.popitem(last=False)
            i += 1

    def clear(self):
        self.cache.clear()

    def get(self, key, default=None):
        try:
            return self.__getitem__(key)
        except KeyError:
            return default

class KeyedAsyncLocks(collections.abc.Collection):
    """
    asyncio.Lock with names.
    Automatically create and delete locks for specified names.
    """
    def __init__(self):
        self.locks = weakref.WeakValueDictionary()

    def __len__(self) -> int:
        return len(self.locks)

    def __getitem__(self, item) -> 'tornado.locks.Lock':
        lock = self.locks.get(item)
        if lock is None:
            self.locks[item] = lock = tornado.locks.Lock()
        return lock

    def __delitem__(self, key) -> None:
        try:
            del self.locks[key]
        except KeyError:
            pass

    def __iter__(self):
        return iter(self.locks)

    def __contains__(self, item):
        return item in self.locks

    def keys(self):
        return self.locks.keys()

    def items(self):
        return self.locks.items()

class TileProvider:
    sgn = (1, 1)
    has_metadata = False
    retry_on_error = False

    def __init__(self, name, url, url2x=None, servers=None, cache=None, attrs=None):
        self.name = name
        self.url = url
        self.url2x = url2x
        self.servers = servers
        self.cache = cache
        self.attrs = attrs or {}

    def __contains__(self, item):
        return item in self.attrs

    def __getitem__(self, key):
        return self.attrs[key]

    def get(self, key, default=None):
        return self.attrs.get(key, default)

    def fast_offset_check(self, z):
        return True

    async def check_metadata(self, headers=None, no_cache=False):
        return {}

    def offset(self, x, y, z):
        return (x, y, z)

    def get_url(self, x, y, z, retina=False):
        url = self.url2x if retina and self.url2x else self.url
        return url.format(
            s=(random.choice(self.servers) if self.servers else ''),
            x=x, y=y, z=z, x4=(x>>4), y4=(y>>4),
            xm=str(x).replace('-', 'M'), ym=str(y).replace('-', 'M'),
            t=int(time.time() * 1000))

class TMSTileProvider(TileProvider):
    sgn = (1, -1)

    def fast_offset_check(self, z):
        return False

    def offset(self, x, y, z):
        return (x, 2**z - 1 - y, z)

class GCJTileProvider(TileProvider):

    def fast_offset_check(self, z):
        return (z < 8)

    def offset(self, x, y, z):
        if z < 8:
            return (x, y, z)
        realpos = prcoords.wgs_gcj(num2deg(x, y, z), True)
        realx, realy = deg2num(zoom=z, *realpos)
        return (realx, realy, z)

class QQTileProvider(TileProvider):
    sgn = (1, -1)

    def fast_offset_check(self, z):
        return False

    def offset(self, x, y, z):
        if z < 8:
            return (x, 2**z - 1 - y, z)
        realpos = prcoords.wgs_gcj(num2deg(x, y+1, z), True)
        realx, realy = deg2num(zoom=z, *realpos)
        return (realx, 2**z - realy, z)

class BaiduTileProvider(TileProvider):
    sgn = (1, -1)

    def fast_offset_check(self, z):
        return False

    @staticmethod
    def bd_merc(lat, lon):
        # Baidu uses EPSG:7008, Clarke 1866
        # PROJ:
        # +proj=merc +a=6378206.4 +b=6356583.8 +lat_ts=0.0 +lon_0=0.0
        # +x_0=0 +y_0=0 +k=1.0 +units=m +nadgrids=@null +wktext +no_defs
        a = 6378206.4
        e = 0.08227185422300325876963654309
        x = math.radians(lon) * a
        phi = math.radians(lat)
        y = (math.asinh(math.tan(phi)) - e * math.atanh(e * math.sin(phi))) * a
        return (x, y)

    def offset(self, x, y, z):
        realpos = prcoords.wgs_bd(num2deg(x, y+1, z), True)
        if 'upscale' not in self.attrs:
            z += 1
        x, y = self.bd_merc(*realpos)
        factor = 2**(z - 18 - 8)
        return (x * factor, y * factor, z)

class ArcGISMapServerProvider(TileProvider):
    sgn = (1, 1)
    has_metadata = True
    no_offset = True

    def __init__(self, name, url, cache=None, attrs=None):
        self.name = name
        self.url = url
        self.cache = cache
        self.attrs = attrs or {}
        self.metadata = None
        self.metadata_lock = tornado.locks.Lock()

    def fast_offset_check(self, z):
        if not self.metadata or not self.no_offset:
            return False
        return bool(self.metadata.get('no_offset'))

    async def get_metadata(self, headers=None, no_cache=False):
        if not no_cache:
            if self.metadata is not None:
                return
            cached_metadata = self.cache.get_meta(self.name)
            if cached_metadata is not None:
                self.metadata = cached_metadata
                return
        client = tornado.curl_httpclient.CurlAsyncHTTPClient()
        response = await client.fetch(
            self.url + '?f=json',
            headers=headers, connect_timeout=10, ca_certs=CA_CERTS,
            proxy_host=CONFIG.get('proxy_host'), proxy_port=CONFIG.get('proxy_port'),
            prepare_curl_callback=(prepare_curl_socks5
                if 'socks5' == CONFIG.get('proxy_type') else None)
        )
        if response.code != 200:
            raise RuntimeError("Can't get metadata: code %s" % response.code)
        d = json.loads(response.body.decode('utf-8', errors='ignore'))
        if not d.get('singleFusedMapCache'):
            raise ValueError("Not tiled map")
        tile_info = d['tileInfo']
        spref = tile_info.get('spatialReference', {})
        srid = spref.get('latestWkid', spref.get('wkid', 4326))
        if srid == 102100:
            srid = 3857
        if srid not in (4326, 3857):
            raise RuntimeError("Unsupported SRID: %s" % self.metadata['srid'])
        self.metadata = {
            'size': (tile_info['cols'], tile_info['rows']),
            'srid': srid,
            'origin': (tile_info['origin']['x'], tile_info['origin']['y']),
            'levels': sorted(
                (level['level'], level['resolution']*tile_info['rows'])
                for level in tile_info['lods']
            ),
            'no_offset': False
        }
        if (srid == 3857 and self.no_offset and
            math.isclose(-ORIGIN_3857, self.metadata['origin'][0]) and
            math.isclose(ORIGIN_3857, self.metadata['origin'][1])):
            no_offset = True
            for level, resolution in self.metadata['levels']:
                req_resolution = RES_3857 / 2 ** level
                if not math.isclose(resolution, req_resolution, rel_tol=1/256):
                    no_offset = False
                    break
            self.metadata['no_offset'] = no_offset
        self.cache.set_meta(self.name, self.metadata)

    async def check_metadata(self, headers=None, no_cache=False):
        async with self.metadata_lock:
            await self.get_metadata(headers, no_cache)
        return {}

    def convert_z(self, x, y, z, srid):
        if srid == 3857:
            req_resolution = RES_3857 / 2 ** z
        elif srid == 4326:
            lat0, lon0 = num2deg(x, y, z)
            lat1, lon1 = num2deg(x + 1, y + 1, z)
            req_resolution = math.sqrt(abs(lat1 - lat0) * abs(lon1 - lon0))
        level = resolution = up_res = None
        for level, resolution in self.metadata['levels']:
            if abs(resolution - req_resolution) / req_resolution < 1/256:
                return level, resolution
            elif resolution < req_resolution:
                break
            up_res = (level, resolution)
        if 'upscale' in self.attrs and up_res is not None:
            return up_res
        return level, resolution

    @staticmethod
    def offset_latlon(lat, lon):
        return (lat, lon)

    def offset(self, x, y, z):
        realpos = tuple(reversed(self.offset_latlon(*num2deg(x, y, z))))
        if self.metadata['srid'] == 3857:
            realpos = from4326_to3857(*realpos)
        tilez, resolution = self.convert_z(x, y, z, self.metadata['srid'])
        if tilez is None:
            return (None, None, None)
        ox, oy = self.metadata['origin']
        tilex = ((realpos[0] - ox) / resolution)
        tiley = -((realpos[1] - oy) / resolution)
        return (tilex, tiley, tilez)

    def get_url(self, x, y, z, retina=False):
        return '{url}/tile/{z}/{y}/{x}'.format(url=self.url, x=x, y=y, z=z)

class TiandituTileProvider(TileProvider):
    has_metadata = True
    retry_on_error = True
    re_ticket = re.compile(r'tk=([0-9A-Za-z]+)')

    def __init__(self, *args, **kwargs):
        super().__init__(*args, **kwargs)
        self.metadata = None
        self.metadata_lock = tornado.locks.Lock()

    async def get_metadata(self, headers=None, no_cache=False):
        if not no_cache:
            if self.metadata is not None:
                return self.metadata['cookies']
            cached_metadata = self.cache.get_meta(self.name)
            if cached_metadata is not None:
                self.metadata = cached_metadata
                return self.metadata['cookies']
        client = tornado.curl_httpclient.CurlAsyncHTTPClient()
        response = await client.fetch(
            'https://map.tianditu.gov.cn/2020/',
            headers=headers, connect_timeout=10, ca_certs=CA_CERTS,
            proxy_host=CONFIG.get('proxy_host'), proxy_port=CONFIG.get('proxy_port'),
            prepare_curl_callback=(prepare_curl_socks5
                if 'socks5' == CONFIG.get('proxy_type') else None)
        )
        if response.code != 200:
            raise RuntimeError("Can't get metadata: code %s" % response.code)
        match = self.re_ticket.search(
            response.body.decode('utf-8', errors='ignore'))
        if not match:
            raise RuntimeError("Can't find ticket")
        cookies = []
        for cookie in response.headers.get_list("Set-Cookie"):
            cookies.append(cookie.rsplit(';', 1)[0].strip())
        self.metadata = {'ticket': match.group(1), 'cookies': cookies}
        self.cache.set_meta(self.name, self.metadata)
        return self.metadata['cookies']

    async def check_metadata(self, headers=None, no_cache=False):
        async with self.metadata_lock:
            cookies = await self.get_metadata(headers, no_cache)
        if headers and headers.get('Cookie'):
            cookies.insert(0, headers['Cookie'])
        return {
            'Cookie': '; '.join(cookies),
            'Referer': 'https://map.tianditu.gov.cn/'
        }

    def get_url(self, x, y, z, retina=False):
        return self.url.format(
            s=(random.choice(self.servers) if self.servers else ''),
            x=x, y=y, z=z, tk=self.metadata['ticket'])

class GCJMapServerProvider(ArcGISMapServerProvider):
    no_offset = False

    @staticmethod
    def offset_latlon(lat, lon):
        return prcoords.wgs_gcj((lat, lon), True)

class TiandituShanghaiMapServerProvider(ArcGISMapServerProvider):
    no_offset = False

    @staticmethod
    def offset_latlon(lat, lon):
        o_lon = 121.3
        # o_lat = 31.2
        bK = 1.006
        V = 1.0
        bN = 0.99
        bm = 0.0
        x1 = 0.5
        x2 = 1.0
        v = (V - bK) / (x1 - bm)
        bk = V - v * x1
        j = (bN - V) / (x2 - x1)
        bo = bN - j * (x2 - x1)
        x_sgn = 1 if lon > o_lon else -1
        d_lon = abs(lon - o_lon)
        if d_lon < x1:
            f = v * d_lon + bk
            d_lon = f * d_lon
            x = o_lon + d_lon * x_sgn
            lon = x
        elif d_lon > x1 and d_lon < x2:
            d_lon = d_lon - x1
            f = j * d_lon + bo
            d_lon = f * d_lon
            lon = o_lon + x1 * x_sgn + d_lon * x_sgn
        return (lat, lon)


SRC_TYPE = {
    'xyz': TileProvider,
    'tms': TMSTileProvider,
    'gcj': GCJTileProvider,
    'qq': QQTileProvider,
    'bd': BaiduTileProvider,
    'baidu': BaiduTileProvider,
    'arcgis': ArcGISMapServerProvider,
    'arcgis_gcj': GCJMapServerProvider,
    'tianditu': TiandituTileProvider,
    'shtdt': TiandituShanghaiMapServerProvider,
}
TILE_SOURCE_CACHE = {}
TILE_GET_LOCKS = KeyedAsyncLocks()

def load_config():
    global APIS, TILE_SOURCE_CACHE, CONFIG
    if APIS:
        return
    config = configparser.ConfigParser(interpolation=None)
    config.read(CONFIG_FILE, 'utf-8')
    cfg = dict(config['CONFIG'])
    cfg['port'] = int(cfg['port'])
    cfg['cache_size'] = int(cfg['cache_size'])
    cfg['cache_ttl'] = int(cfg['cache_ttl'])
    cfg['cache_realtime_ttl'] = int(cfg.get('cache_realtime_ttl', 60))
    if 'proxy_port' in cfg:
        cfg['proxy_port'] = int(cfg['proxy_port'])
    CONFIG = cfg
    if cfg.get('cache_db'):
        TILE_SOURCE_CACHE = DBTileCache(
            cfg['cache_db'], cfg['cache_size'], cfg['cache_ttl'])
    else:
        TILE_SOURCE_CACHE = MemoryTileCache(cfg['cache_size'], cfg['cache_ttl'])
    APIS = collections.OrderedDict()
    for name, cfgsection in config.items():
        if name in ('DEFAULT', 'CONFIG'):
            continue
        section = dict(cfgsection)
        src_type = section.get('type', section.get('offset', 'xyz'))
        cls = SRC_TYPE.get(src_type)
        if cls is None:
            raise ValueError('unknown source API type: %s' % src_type)
        kwargs = {'url': section.pop('url'), 'cache': TILE_SOURCE_CACHE}
        if 'url2x' in section:
            kwargs['url2x'] = section.pop('url2x')
        if 's' in section:
            kwargs['servers'] = section.pop('s').split(',')
        kwargs['attrs'] = section
        APIS[name] = cls(name, **kwargs)

def num2deg(xtile, ytile, zoom):
    n = 2 ** zoom
    lat = math.degrees(math.atan(math.sinh(math.pi * (1 - 2 * ytile / n))))
    lon = xtile / n * 360 - 180
    return (lat, lon)

def deg2num(lat, lon, zoom):
    n = 2 ** zoom
    xtile = ((lon + 180) / 360 * n)
    ytile = (1 - math.asinh(math.tan(math.radians(lat))) / math.pi) * n / 2
    return (xtile, ytile)

def is_empty(im):
    extrema = im.getextrema()
    if len(extrema) >= 3:
        if len(extrema) > 3 and extrema[-1] == (0, 0):
            return True
        for ext in extrema[:3]:
            if ext != (0, 0):
                return False
        return True
    else:
        return extrema[0] == (0, 0)

def stitch_tiles(tiles, corners, bbox, grid, sgnxy, name):
    ims = []
    size = orig_format = orig_mode = None
    for b, _ in tiles:
        if b:
            im = Image.open(io.BytesIO(b))
            ims.append(im)
            size = im.size
            orig_format = im.format
            orig_mode = im.mode
        else:
            ims.append(None)
    if not size:
        return None, None
    mode = 'RGB' if orig_mode == 'RGB' else 'RGBA'
    newim = Image.new(mode, (
        size[0]*(bbox[2]-bbox[0]), size[1]*(bbox[3]-bbox[1])))
    mesh = calc_pil_mesh(sgnxy, size, bbox, grid)
    for i, xy in enumerate(corners):
        if ims[i] is None:
            continue
        xy0 = (size[0]*xy[0][0], size[1]*xy[1][0])
        if mode == 'RGB':
            newim.paste(ims[i], xy0)
        else:
            im = ims[i]
            if im.mode != mode:
                im = im.convert(mode)
            if is_empty(im):
                newim.paste((0,0,0,0), xy0 + (xy0[0]+size[0], xy0[1]+size[1]))
            else:
                newim.paste(im, xy0)
        ims[i].close()
    del ims
    retim = newim.transform(size, Image.MESH, mesh, resample=Image.BICUBIC)
    if retim.mode == 'RGBA' and retim.getextrema()[3][0] >= 252:
        retim = retim.convert('RGB')
    newim.close()
    del newim
    retb = io.BytesIO()
    mime_type = tiles[0][1]
    if orig_format == 'JPEG':
        retim.save(retb, 'JPEG', quality=93)
        mime_type = 'image/jpeg'
    else:
        # if orig_mode == 'P':
            # retim = retim.quantize(colors=256)
        retim.save(retb, orig_format)
        if orig_format == 'PNG':
            mime_type = 'image/png'
    retim.close()
    del retim
    return retb.getvalue(), mime_type

async def get_tile(source, z, x, y, retina=False, client_headers=None):
    api = APIS[source]
    x = int(x)
    y = int(y)
    cache_key = '%s%s/%d/%d/%d' % (source, '@2x' if retina else '', z, x, y)
    async with TILE_GET_LOCKS[cache_key]:
        res = TILE_SOURCE_CACHE.get(cache_key)
        if res:
            return res
        realtime = api.get('realtime')
        req_headers = client_headers.copy() or {}
        client_kwargs = {
            'headers': req_headers,
            'connect_timeout': 10,
            'ca_certs': CA_CERTS,
            'proxy_host': CONFIG.get('proxy_host'),
            'proxy_port': CONFIG.get('proxy_port'),
            'prepare_curl_callback': (
                prepare_curl_socks5 if 'socks5' == CONFIG.get('proxy_type')
                else None
            )
        }
        if 'referer' in api:
            req_headers['Referer'] = api['referer']
        if api.has_metadata:
            req_headers.update(await api.check_metadata(req_headers))
        url = api.get_url(x, y, z, retina)
        try:
            response = await HTTP_CLIENT.fetch(url, **client_kwargs)
        except tornado.httpclient.HTTPClientError as ex:
            if ex.code == 404:
                return (None, None)
            elif 400 <= ex.code < 500:
                raise
            elif api.retry_on_error or ex.code == 503:
                if api.has_metadata:
                    req_headers.update(await api.check_metadata(req_headers, True))
                response = await HTTP_CLIENT.fetch(url, **client_kwargs)
            elif ex.code >= 500:
                raise
        res = (response.body, response.headers['Content-Type'])
        del response
        if realtime:
            TILE_SOURCE_CACHE.save(
                cache_key, res, CONFIG.get('cache_realtime_ttl', 0))
        else:
            TILE_SOURCE_CACHE[cache_key] = res
        return res

def calc_grid(x, y, z, sgnxy, off_fn, grid_num=8):
    sgnx, sgny = sgnxy
    sx0, sx1 = sorted((x, x+sgnx))
    sy0, sy1 = sorted((y, y+sgny))
    bbox = [float('inf'), float('inf'), float('-inf'), float('-inf')]
    grid = []
    tz = z
    for i in range(grid_num+1):
        gx = sx0 + i / grid_num
        column = []
        for j in range(grid_num+1):
            gy = sy0 + j / grid_num
            tx, ty, tz = off_fn(gx, gy, z)
            column.append((gx - sx0, gy - sy0, tx, ty))
            if i == 0 or i == grid_num:
                bbox[0] = min(bbox[0], tx)
                bbox[2] = max(bbox[2], tx)
            if j == 0 or j == grid_num:
                bbox[1] = min(bbox[1], ty)
                bbox[3] = max(bbox[3], ty)
        grid.append(column)
    bbox = [
        math.floor(bbox[0]), math.floor(bbox[1]),
        math.ceil(bbox[2]), math.ceil(bbox[3]),
    ]
    return bbox, grid, tz

def calc_pil_mesh(sgnxy, size, bbox, grid):
    sgnx, sgny = sgnxy
    szx, szy = size
    dx = -bbox[0] if sgnx == 1 else bbox[2]
    dy = -bbox[1] if sgny == 1 else bbox[3]
    pil_mesh = []
    for i, column in enumerate(grid[1:], 1):
        for j, coords in enumerate(column[1:], 1):
            sx0, sy0, tx0, ty0 = grid[i-1][j-1]
            sx1, sy1, tx1, ty1 = coords
            pil_mesh.append((
                (int(sx0 * szx), int(sy0 * szy),
                 int(sx1 * szx), int(sy1 * szy)),
                ((tx0 * sgnx + dx) * szx, (ty0 * sgny + dy) * szy,
                 (tx0 * sgnx + dx) * szx, (ty1 * sgny + dy) * szy,
                 (tx1 * sgnx + dx) * szx, (ty1 * sgny + dy) * szy,
                 (tx1 * sgnx + dx) * szx, (ty0 * sgny + dy) * szy)
            ))
    return pil_mesh


async def draw_tile(source, z, x, y, retina=False, client_headers=None):
    api = APIS[source]
    retina = ('url2x' in api and retina)
    if api.fast_offset_check(z):
        res = await get_tile(source, z, x, y, retina, client_headers)
        return res
    else:
        if api.has_metadata:
            await api.check_metadata(client_headers)
        sgnxy = api.sgn
        bbox, grid, realz = calc_grid(x, y, z, sgnxy, api.offset)
        if (bbox[2] - bbox[0] == 1) and (bbox[3] - bbox[1] == 1):
            realx = bbox[0] if sgnxy[0] == 1 else bbox[2] - 1
            realy = bbox[1] if sgnxy[1] == 1 else bbox[3] - 1
            res = await get_tile(source, realz, realx, realy,
                                 retina, client_headers)
            return res
        futures = []
        if sgnxy[0] == 1:
            x_range = enumerate(range(bbox[0], bbox[2]))
        else:
            x_range = enumerate(range(bbox[2] - 1, bbox[0] - 1, -1))
        if sgnxy[1] == 1:
            y_range = enumerate(range(bbox[1], bbox[3]))
        else:
            y_range = enumerate(range(bbox[3] - 1, bbox[1] - 1, -1))
        corners = tuple(itertools.product(x_range, y_range))
        for x1, y1 in corners:
            futures.append(get_tile(
                source, realz, x1[1], y1[1], retina, client_headers))
        tiles = await tornado.gen.multi(futures)
        del futures
        ioloop = tornado.ioloop.IOLoop.current()
        result = await ioloop.run_in_executor(None, stitch_tiles,
            tiles, corners, bbox, grid, sgnxy, source)
        del tiles, corners, bbox, grid
        return result


class MainHandler(tornado.web.RequestHandler):
    def get(self):
        html = (
            '<!DOCTYPE html><html><head><title>TMS Tile Proxy Server</title>'
            '</head><body><h1>TMS Tile Proxy Server</h1>'
            '<h2><a href="/map">Demo</a></h2>'
            '<h2>Endpoints</h2><dl>%s</dl></body></html>'
        ) % ''.join('<dt>%s</dt><dd>/%s/{z}/{x}/{y}%s</dd>' % (
            APIS[s].get('name', s), s, '{@2x}' if 'url2x' in APIS[s] else ''
        ) for s in APIS)
        self.write(html)

class TestHandler(tornado.web.RequestHandler):
    def get(self):
        TEST_TILES = ('14/13518/6396', '4/14/8', '8/203/132', '9/430/240')
        html = (
            '<!DOCTYPE html><html><head><title>TMS Tile Proxy Server</title>'
            '</head><body>%s</body></html>'
        ) % ''.join('<p>%s</p><p>%s</p>' % (
            ''.join('<img src="/%s/%s" title="%s">' % (s, tile, s) for s in APIS),
            ''.join('<img src="/%s/%s@2x" title="%s">' % (s, tile, s) for s in APIS
                if 'url2x' in APIS[s])
        ) for tile in TEST_TILES)
        self.write(html)

class RobotsTxtHandler(tornado.web.RequestHandler):
    def get(self):
        txt = 'User-agent: *\nDisallow: /\n'
        self.set_header('Content-Type', 'text/plain; charset=UTF-8')
        self.write(txt)

class DemoHandler(tornado.web.RequestHandler):
    def get(self):
        layers_base = []
        layers_overlay = []
        for k, v in APIS.items():
            obj = {'url': '/%s/{z}/{x}/{y}%s' % (k, '{r}' if 'url2x' in v else ''),
                   'name': v.get('name', k),
                   'attribution': v.get('attribution', '')}
            if 'url2x' in v:
                obj['url2x'] = v['url2x']
            if 'annotation' in v:
                layers_overlay.append(obj)
            else:
                layers_base.append(obj)
        layers_attr = json.dumps([layers_base, layers_overlay], separators=(',', ':'))
        with open('demo.html', 'r', encoding='utf-8') as f:
            html = f.read().replace('{{layers}}', layers_attr)
        self.write(html)

class TMSHandler(tornado.web.RequestHandler):
    def initialize(self, *args, **kwargs):
        self.headers = self.request.headers

    async def get(self, name, z, x, y, retina):
        if name not in APIS:
            raise tornado.web.HTTPError(404)
        try:
            client_headers = {
                k:v for k,v in self.request.headers.items()
                if k in HEADERS_WHITELIST
            }
            res = await draw_tile(
                name, int(z), int(x), int(y), bool(retina), client_headers)
        #except tornado.httpclient.HTTPError as ex:
            # raise tornado.web.HTTPError(502)
        #except KeyError:
            #raise tornado.web.HTTPError(404)
        except Exception:
            raise
        if not res[0]:
            raise tornado.web.HTTPError(404)
        if APIS[name].get('realtime'):
            cache_ttl = CONFIG.get('cache_realtime_ttl', 0)
        else:
            cache_ttl = CONFIG['cache_ttl']
        self.set_header('Content-Type', res[1])
        self.set_header('Cache-Control', 'max-age=%d' % cache_ttl)
        self.write(res[0])

def make_app():
    load_config()
    return tornado.web.Application([
        (r"/", MainHandler),
        (r"/test", TestHandler),
        (r"/map", DemoHandler),
        (r"/([^/]+)/(\d+)/(-?\d+)/(-?\d+)((?:@2x)?)", TMSHandler),
        (r"/robots.txt", RobotsTxtHandler),
    ])

if __name__ == '__main__':
    app = make_app()
    app.listen(CONFIG['port'], CONFIG['listen'])
    ioloop = tornado.ioloop.IOLoop.current()
    ioloop.set_default_executor(
        concurrent.futures.ThreadPoolExecutor(max_workers=os.cpu_count()))
    ioloop.start()
