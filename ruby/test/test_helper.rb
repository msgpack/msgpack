require 'test/unit'
begin
require File.dirname(__FILE__) + '/../msgpack'
rescue LoadError
require File.dirname(__FILE__) + '/../lib/msgpack'
end

GC.stress = true
