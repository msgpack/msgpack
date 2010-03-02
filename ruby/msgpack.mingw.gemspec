Gem::Specification.new do |s|
  s.platform = Gem::Platform::CURRENT
  s.name = "msgpack"
  s.version = "0.3.3"
  s.summary = "MessagePack, a binary-based efficient data interchange format."
  s.author = "FURUHASHI Sadayuki"
  s.email = "frsyuki@users.sourceforge.jp"
  s.homepage = "http://msgpack.sourceforge.jp/"
  s.rubyforge_project = "msgpack"
  s.has_rdoc = false
  s.extra_rdoc_files = ["README", "ChangeLog", "AUTHORS"]
  s.require_paths = ["lib", "ext"]
  s.files = Dir["lib/**/*", "ext/**/*", "msgpack/**/*", "test/**/*"]
  s.test_files = Dir["test/test_*.rb"]
  s.extensions = Dir["ext/**/extconf.rb"]
end
