require 'msgpack'

serialized = [1, -1, true, false, nil, {"key" => "value"}].to_msgpack
p MessagePack.unpack(serialized)

