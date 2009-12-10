Gem::Specification.new do |s|
  s.platform = Gem::Platform::CURRENT
  s.name = "msgpack"
  s.version = "0.3.2"
  s.summary = "MessagePack"
  s.author = "FURUHASHI Sadayuki"
  s.email = "frsyuki@users.sourceforge.jp"
  s.homepage = "http://msgpack.sourceforge.jp/"
  s.rubyforge_project = "msgpack"
  s.require_paths = ["lib", "ext"]
  s.files = ["lib/**/*", "ext/**/*"].map {|g| Dir.glob(g) }.flatten
end
