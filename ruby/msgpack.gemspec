require './version.rb'
Gem::Specification.new do |s|
  s.platform = Gem::Platform::RUBY
  s.name = "msgpack"
  s.version = MessagePack::VERSION
  s.summary = "MessagePack, a binary-based efficient data interchange format."
  s.author = "FURUHASHI Sadayuki"
  s.email = "frsyuki@users.sourceforge.jp"
  s.homepage = "http://msgpack.org/"
  s.rubyforge_project = "msgpack"
  s.has_rdoc = true
	s.rdoc_options = ["ext"]
  s.require_paths = ["lib"]
  s.files = Dir["ext/**/*", "msgpack/**/*", "test/**/*"]
  s.test_files = Dir["test/test_*.rb"]
  s.extensions = Dir["ext/**/extconf.rb"]
end
