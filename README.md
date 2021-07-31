# cntms
[Tile Map Server](https://wiki.openstreetmap.org/wiki/Slippy_map_tilenames) reverse proxy with coordinates regularization.

This TMS proxy solves the problems that map services in China geneally have distorted coordinates. It stitches the upstream tiles to make standard EPSG:3857 tiles. This proxy also caches tile images.

Supports: Baidu, Tencent, Gaode, Google, GeoQ, Tianditu, OpenStreetMap and ArcGIS MapServer.

Edit `tmsapi.ini` to set listen address, port, cache size, and upstream APIs.

Use this software at your own risk.

---

纠偏[瓦片地图](https://wiki.openstreetmap.org/wiki/Slippy_map_tilenames)代理，可修复图块中 GCJ02、BD09 等坐标系的偏移。可用于 GIS 软件、网页地图等。

配置文件在 `tmsapi.ini`。请自行架设服务器，请勿滥用，风险自担。

