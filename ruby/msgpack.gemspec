Gem::Specification.new do |s|
  s.platform = Gem::Platform::CURRENT
  s.name = "msgpack"
  s.version = "0.2.2"
  s.summary = "MessagePack"
  s.author = "FURUHASHI Sadayuki"
  s.email = "frsyuki _at_ users.sourceforge.jp"
  s.homepage = "https://launchpad.net/msgpack/"
  s.require_paths = ["lib", "ext"]
  s.files = ["lib/**/*", "ext/**/*"].map {|g| Dir.glob(g) }.flatten
end
