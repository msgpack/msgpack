# coding: utf-8
from msgpack._msgpack import *

# alias for compatibility to simplejson/marshal/pickle.
load = unpack
loads = unpackb

dump = pack
dumps = packb

