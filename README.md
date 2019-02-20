# cntms
Tile Map Server reverse proxy with coordinates regularization.

This TMS proxy solves the problems that map services in China geneally have distorted coordinates. It stitches the upstream tiles to make standard EPSG:3857 tiles. This proxy also caches tile images.

Supports: Baidu, Tencent, Gaode, Google, GeoQ, Tianditu, and OpenStreetMap.

Edit `tmsapi.ini` to set listen address, port, cache size, and upstream APIs.

Use this software at your own risk.
