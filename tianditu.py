#!/usr/bin/env python3
# -*- coding: utf-8 -*-

import os
import re
import sys
import json
import random

import tornado.web
import tornado.gen
import tornado.locks
import tornado.ioloop
import tornado.curl_httpclient

try:
    import certifi
    CA_CERTS = certifi.where()
except ImportError:
    CA_CERTS = None

LAYERS = ('vec_w', 'cva_w', 'img_w', 'cia_w', 'ter_w', 'cta_w')
HTTP_CLIENT = tornado.curl_httpclient.CurlAsyncHTTPClient()
HEADERS_WHITELIST = {
    'Access-Control-Allow-Origin',
    'Cache-Control',
    'Content-Type',
    'Date',
    'Expires',
    'Server',
    'Set-Cookie',
}
re_ticket = re.compile(r'tk=([0-9A-Za-z]+)')


class DemoHandler(tornado.web.RequestHandler):
    def get(self):
        layers_base = []
        layers_overlay = []
        for name in LAYERS:
            obj = {'url': '/%s/{z}/{x}/{y}' % name,
                   'name': name,
                   'attribution': '天地图'}
            if name[0] == 'c':
                layers_overlay.append(obj)
            else:
                layers_base.append(obj)
        layers_attr = json.dumps([layers_base, layers_overlay], separators=(',', ':'))
        with open('demo.html', 'r', encoding='utf-8') as f:
            html = f.read().replace('{{layers}}', layers_attr)
        self.write(html)


class TiandituHandler(tornado.web.RequestHandler):
    lock = tornado.locks.Lock()
    base_url = 'https://map.tianditu.gov.cn/'
    url = 'https://t{s}.tianditu.gov.cn/{name}/wmts?SERVICE=WMTS&REQUEST=GetTile&VERSION=1.0.0&LAYER={layer}&STYLE=default&TILEMATRIXSET={mset}&FORMAT=tiles&tk={tk}&TILECOL={x}&TILEROW={y}&TILEMATRIX={z}'
    servers = tuple(range(8))
    ticket = None
    headers = {
        'Accept-Language': 'zh-CN,zh;q=0.8,zh-TW;q=0.6,en;q=0.4',
        'User-Agent': 'Mozilla/5.0 (Windows NT 6.1; Win64; x64; rv:88.0) Gecko/20100101 Firefox/88.0',
        'Referer': 'https://map.tianditu.gov.cn/'
    }

    async def get_ticket(self):
        response = await HTTP_CLIENT.fetch(
            self.base_url, headers=self.headers, connect_timeout=20,
            ca_certs=CA_CERTS)
        if response.code != 200:
            raise RuntimeError("Can't fetch main page")
        match = re_ticket.search(response.body.decode('utf-8', errors='ignore'))
        if not match:
            raise RuntimeError("Can't find ticket")
        type(self).ticket = match.group(1)
        cookies = []
        for cookie in response.headers.get_list("Set-Cookie"):
            cookies.append(cookie.rsplit(';', 1)[0])
        if cookies:
            type(self).headers['Cookie'] = '; '.join(cookies)

    async def get(self, name, z, x, y):
        async with self.lock:
            if self.ticket is None:
                await self.get_ticket()
        layer, mset = name.rsplit('_', 1)
        url = self.url.format(
            s=random.choice(self.servers), name=name, layer=layer, mset=mset,
            tk=self.ticket, x=x, y=y, z=z
        )
        response = await HTTP_CLIENT.fetch(
            url, headers=self.headers, connect_timeout=20, ca_certs=CA_CERTS)
        if response.code >= 400:
            type(self).ticket = None
        else:
            cookies = []
            for cookie in response.headers.get_list("Set-Cookie"):
                cookies.append(cookie.rsplit(';', 1)[0])
            if cookies:
                type(self).headers['Cookie'] = '; '.join(cookies)
        self.set_status(response.code)
        for name, value in response.headers.get_all():
            if name in HEADERS_WHITELIST:
                self.set_header(name, value)
        self.write(response.body)

def make_app():
    return tornado.web.Application([
        (r"/", DemoHandler),
        (r"/([^/]+)/(\d+)/(-?\d+)/(-?\d+)", TiandituHandler),
    ])

if __name__ == '__main__':
    if len(sys.argv) > 1:
        listen, port = sys.argv[1].rsplit(':', 1)
        port = int(port)
    else:
        listen = '127.0.0.1'
        port = 6701
    app = make_app()
    app.listen(port, listen)
    ioloop = tornado.ioloop.IOLoop.current()
    ioloop.start()
