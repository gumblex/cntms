#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import io
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
import tornado.curl_httpclient
from PIL import Image

try:
    import certifi
    CA_CERTS = certifi.where()
except ImportError:
    CA_CERTS = None

# Earth mean radius
R_EARTH = 6371000
EARTH_EQUATORIAL_RADIUS = 6378137

CONFIG_FILE = 'tmsapi.ini'
CONFIG = {}
APIS = None

BD_LL2MC = (
    (-0.0015702102444, 111320.7020616939, 1704480524535203, -10338987376042340, 26112667856603880, -35149669176653700, 26595700718403920, -10725012454188240, 1800819912950474, 82.5),
    (0.0008277824516172526, 111320.7020463578, 647795574.6671607, -4082003173.641316, 10774905663.51142, -15171875531.51559, 12053065338.62167, -5124939663.577472, 913311935.9512032, 67.5),
    (0.00337398766765, 111320.7020202162, 4481351.045890365, -23393751.19931662, 79682215.47186455, -115964993.2797253, 97236711.15602145, -43661946.33752821, 8477230.501135234, 52.5),
    (0.00220636496208, 111320.7020209128, 51751.86112841131, 3796837.749470245, 992013.7397791013, -1221952.21711287, 1340652.697009075, -620943.6990984312, 144416.9293806241, 37.5),
    (-0.0003441963504368392, 111320.7020576856, 278.2353980772752, 2485758.690035394, 6070.750963243378, 54821.18345352118, 9540.606633304236, -2710.55326746645, 1405.483844121726, 22.5),
    (-0.0003218135878613132, 111320.7020701615, 0.00369383431289, 823725.6402795718, 0.46104986909093, 2351.343141331292, 1.58060784298199, 8.77738589078284, 0.37238884252424, 7.45)
)

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

class TileCache(collections.abc.MutableMapping):

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

    def __setitem__(self, key, value):
        now = int(time.time())
        self.db.execute('REPLACE INTO cache VALUES (?,?,?,?,?)',
            (key, now+self.ttl, now, value[1], value[0]))
        self.expire()

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

TILE_SOURCE_CACHE = {}
TILE_GET_LOCKS = KeyedAsyncLocks()

def load_config():
    global APIS, TILE_SOURCE_CACHE, CONFIG
    if APIS:
        return
    config = configparser.ConfigParser(interpolation=None)
    config.read(CONFIG_FILE, 'utf-8')
    APIS = collections.OrderedDict()
    for name, cfgsection in config.items():
        if name in ('DEFAULT', 'CONFIG'):
            continue
        section = dict(cfgsection)
        if 's' in section:
            section['s'] = section['s'].split(',')
        APIS[name] = section
    cfg = dict(config['CONFIG'])
    cfg['port'] = int(cfg['port'])
    cfg['cache_size'] = int(cfg['cache_size'])
    cfg['cache_ttl'] = int(cfg['cache_ttl'])
    if 'proxy_port' in cfg:
        cfg['proxy_port'] = int(cfg['proxy_port'])
    CONFIG = cfg
    TILE_SOURCE_CACHE = TileCache(
        cfg['cache_db'], cfg['cache_size'], cfg['cache_ttl'])

def num2deg(xtile, ytile, zoom):
    n = 2 ** zoom
    lat = math.degrees(math.atan(math.sinh(math.pi * (1 - 2 * ytile / n))))
    lon = xtile / n * 360 - 180
    return (lat, lon)

def deg2num(lat, lon, zoom):
    lat_r = math.radians(lat)
    n = 2 ** zoom
    xtile = ((lon + 180) / 360 * n)
    ytile = ((1 - math.log(math.tan(lat_r) + 1/math.cos(lat_r)) / math.pi) / 2 * n)
    return (xtile, ytile)

def offset_gcj(x, y, z):
    if z < 8:
        return (x, y, z)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        realpos = prcoords.wgs_gcj(num2deg(x, y, z), True)
        realx, realy = deg2num(zoom=z, *realpos)
        return (realx, realy, z)

def offset_qq(x, y, z):
    if z < 8:
        return (x, 2**z - 1 - y, z)
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        realpos = prcoords.wgs_gcj(num2deg(x, y+1, z), True)
        realx, realy = deg2num(zoom=z, *realpos)
        return (realx, 2**z - realy, z)

def offset_bd(x, y, z):
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        realpos = prcoords.wgs_bd(num2deg(x, y+1, z), True)
    z += 1
    for i, Kj_d in enumerate(range(75, -15, -15)):
        if abs(realpos.lat) >= Kj_d:
            mc = BD_LL2MC[i]
            break
    lng = mc[0] + mc[1] * abs(realpos.lon)
    c = abs(realpos.lat) / mc[9]
    lat = mc[2] + mc[3] * c + mc[4] * c * c + mc[5] * c**3 + mc[6] * c**4 + mc[7] * c**5 + mc[8] * c**6
    lng = math.copysign(lng, realpos.lon)
    lat = math.copysign(lat, realpos.lat)
    x = lng * 2**(z - 18 - 8)
    y = lat * 2**(z - 18 - 8)
    return (x, y, z)

OFFSET_FN = {
    'gcj': offset_gcj,
    'qq': offset_qq,
    'bd': offset_bd
}
OFFSET_SGN = {
    'gcj': (1, 1),
    'qq': (1, -1),
    'bd': (1, -1)
}

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
        url = api['url2x' if retina else 'url'].format(
            s=(random.choice(api['s']) if 's' in api else ''),
            x=x, y=y, z=z, x4=(x>>4), y4=(y>>4),
            xm=str(x).replace('-', 'M'), ym=str(y).replace('-', 'M'),
            t=int(time.time() * 1000))
        if client_headers:
            headers = {k:v for k,v in client_headers.items()
                       if k in HEADERS_WHITELIST}
        else:
            headers = None
        if 'referer' in api:
            headers['Referer'] = api['referer']
        response = await HTTP_CLIENT.fetch(
            url, headers=headers, connect_timeout=10, ca_certs=CA_CERTS,
            proxy_host=CONFIG.get('proxy_host'), proxy_port=CONFIG.get('proxy_port'), 
            prepare_curl_callback=(prepare_curl_socks5 if 'socks5' == CONFIG.get('proxy_type') else None))
        res = (response.body, response.headers['Content-Type'])
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
    if 'offset' not in api or (z < 1 and OFFSET_SGN[api['offset']] == (1, 1)):
        res = await get_tile(source, z, x, y, retina, client_headers)
        return res
    else:
        sgnxy = OFFSET_SGN[api['offset']]
        off_fn = OFFSET_FN[api['offset']]
        bbox, grid, realz = calc_grid(x, y, z, sgnxy, off_fn)
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
        ioloop = tornado.ioloop.IOLoop.current()
        result = await ioloop.run_in_executor(None, stitch_tiles,
            tiles, corners, bbox, grid, sgnxy, source)
        return result


class MainHandler(tornado.web.RequestHandler):
    def get(self):
        html = ('<!DOCTYPE html><html><head><title>TMS Tile Proxy Server</title>'
                '</head><body><h1>TMS Tile Proxy Server</h1>'
                '<h2><a href="/map">Demo</a></h2>'
                '<h2>Endpoints</h2><dl>%s</dl></body></html>') % ''.join(
                '<dt>%s</dt><dd>/%s/{z}/{x}/{y}%s</dd>' % (APIS[s].get('name', s),
                s, '{@2x}' if 'url2x' in APIS[s] else '') for s in APIS)
        self.write(html)

class TestHandler(tornado.web.RequestHandler):
    def get(self):
        TEST_TILES = ('14/13518/6396', '4/14/8', '8/203/132', '9/430/240')
        html = ('<!DOCTYPE html><html><head><title>TMS Tile Proxy Server</title>'
                '</head><body>%s</body></html>' % ''.join('<p>%s</p><p>%s</p>' % (
                ''.join('<img src="/%s/%s" title="%s">' % (s, tile, s) for s in APIS),
                ''.join('<img src="/%s/%s@2x" title="%s">' % (s, tile, s) for s in APIS
                if 'url2x' in APIS[s])) for tile in TEST_TILES))
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
        try:
            res = await draw_tile(
                name, int(z), int(x), int(y), bool(retina), self.request.headers)
        except tornado.httpclient.HTTPError as ex:
            if ex.code == 404:
                raise tornado.web.HTTPError(404)
            else:
                raise
        except Exception:
            raise
        if not res[0]:
            raise tornado.web.HTTPError(404)
        self.set_header('Content-Type', res[1])
        self.set_header('Cache-Control', 'max-age=%d' % CONFIG['cache_ttl'])
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
