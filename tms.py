#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import io
import time
import math
import random
import sqlite3
import warnings
import collections
import configparser

import prcoords
import tornado.web
import tornado.gen
import tornado.ioloop
import tornado.httpclient
from PIL import Image

# Earth mean radius
R_EARTH = 6371000
EARTH_EQUATORIAL_RADIUS = 6378137

CONFIG_FILE = 'tmsapi.ini'
CACHE_DB = 'tmscache.db'
APIS = None


CORNERS = ((0, 0), (0, 1), (1, 0), (1, 1))

HEADERS_WHITELIST = {'User-Agent', 'Accept', 'Accept-Language'}

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
        ')')

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
            'SELECT key FROM cache WHERE expire>=? ORDER BY updated LIMIT ?)',
            (etime or time.time(), self.maxsize))

    def clear(self):
        self.db.execute('DELETE FROM cache')

    def get(self, key, default=None):
        try:
            return self.__getitem__(key)
        except KeyError:
            return default

TILE_SOURCE_CACHE = TileCache(CACHE_DB, 256, 86400)

def load_config():
    global APIS
    if APIS:
        return
    config = configparser.ConfigParser(interpolation=None)
    config.read(CONFIG_FILE)
    APIS = {}
    for name, cfgsection in config.items():
        if name == 'DEFAULT':
            continue
        section = dict(cfgsection)
        if 's' in section:
            section['s'] = section['s'].split(',')
        APIS[name] = section

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
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        realpos = prcoords.wgs_gcj(num2deg(x, y, z), True)
        realxy = deg2num(zoom=z, *realpos)
        return realxy

def offset_qq(x, y, z):
    with warnings.catch_warnings():
        warnings.simplefilter("ignore")
        realpos = prcoords.wgs_gcj(num2deg(x, y, z), True)
        realx, realy = deg2num(zoom=z, *realpos)
        return (realx, (2**z - 1 - realy))

OFFSET_FN = {
    'gcj': offset_gcj,
    'qq': offset_qq
}

def stitch_tiles(tiles, x, y, name):
    xfrac = x - math.floor(x)
    yfrac = y - math.floor(y)
    ims = [Image.open(io.BytesIO(b)) for b, _ in tiles]
    size = ims[0].size
    if ims[0].format == 'PNG':
        mode = 'RGBA'
    else:
        mode = 'RGB'
    newim = Image.new(mode, (size[0]*2, size[1]*2))
    for i, dxy in enumerate(CORNERS):
        newim.paste(ims[i], (size[0]*dxy[0], size[1]*dxy[1]))
    x2 = round(size[0]*xfrac)
    y2 = round(size[1]*yfrac)
    retim = newim.crop((x2, y2, x2+size[0], y2+size[1]))
    retb = io.BytesIO()
    if ims[0].format == 'JPEG':
        retim.save(retb, 'JPEG', quality=92)
    else:
        retim.save(retb, ims[0].format)
    return retb.getvalue(), tiles[0][1]

@tornado.gen.coroutine
def get_tile(source, z, x, y, client_headers=None):
    cache_key = '%s/%d/%d/%d' % (source, z, x, y)
    res = TILE_SOURCE_CACHE.get(cache_key)
    if res:
        return res
    api = APIS[source]
    url = api['url'].format(s=(random.choice(api['s']) if 's' in api else ''),
        x=x, y=y, z=z, x4=(x>>4), y4=(y>>4))
    if client_headers:
        headers = {k:v for k,v in client_headers.items() if k in HEADERS_WHITELIST}
    else:
        headers = None
    client = tornado.httpclient.AsyncHTTPClient()
    response = yield client.fetch(url, headers=headers, connect_timeout=10)
    res = (response.body, response.headers['Content-Type'])
    TILE_SOURCE_CACHE[cache_key] = res
    return res

@tornado.gen.coroutine
def draw_tile(source, z, x, y, client_headers=None):
    api = APIS[source]
    if z < 8 or 'offset' not in api:
        res = yield get_tile(source, z, x, y, client_headers)
        return res
    else:
        realxy = OFFSET_FN[api['offset']](x, y, z)
        futures = []
        for dx1, dy1 in CORNERS:
            x1 = math.floor(realxy[0]) + dx1
            y1 = math.floor(realxy[1]) + dy1
            futures.append(get_tile(source, z, x1, y1, client_headers))
        tiles = yield futures
        return stitch_tiles(tiles, realxy[0], realxy[1], source)


class MainHandler(tornado.web.RequestHandler):
    def get(self):
        html = ('<!DOCTYPE html><html><head><title>TMS Tile Proxy Server</title>'
                '</head><body><p>Endpoints:</p><ul>%s</ul></body></html>') % ''.join(
                '<li>/%s/[z]/[x]/[y]</li>' % s for s in APIS)
        self.write(html)

class TestHandler(tornado.web.RequestHandler):
    def get(self):
        TEST_TILE = '14/13518/6396'
        html = ('<!DOCTYPE html><html><head><title>TMS Tile Proxy Server</title>'
                '</head><body><p>%s</p></body></html>') % ''.join(
                '<img src="/%s/%s" title="%s">' % (s, TEST_TILE, s) for s in APIS)
        self.write(html)

class TMSHandler(tornado.web.RequestHandler):

    def initialize(self, *args, **kwargs):
        self.headers = self.request.headers

    @tornado.gen.coroutine
    def get(self, name, z, x, y):
        try:
            res = yield draw_tile(name, int(z), int(x), int(y), self.request.headers)
        except tornado.httpclient.HTTPError as ex:
            if ex.code == 404:
                raise tornado.web.HTTPError(404)
            else:
                raise
        except Exception:
            raise
        self.set_header('Content-Type', res[1])
        self.set_header('Cache-Control', 'max-age=86400')
        self.write(res[0])

def make_app():
    load_config()
    return tornado.web.Application([
        (r"/", MainHandler),
        (r"/test", TestHandler),
        (r"/([^/]+)/(\d+)/(-?\d+)/(-?\d+)", TMSHandler),
    ])

if __name__ == '__main__':
    app = make_app()
    app.listen(6700)
    tornado.ioloop.IOLoop.current().start()
