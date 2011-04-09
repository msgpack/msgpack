TARGET=msgpack.dll
TEST_TARGET=msgpack.tests.dll

SRC=$(shell find msgpack -name "*.cs")
TEST_SRC=$(shell find msgpack.tests -name "*.cs")

MONO_CC=mcs
NUNIT_CONSOLE=nunit-console

all: $(TARGET)
test: $(TEST_TARGET) $(TARGET)
clean:
	rm -f $(TARGET) $(TEST_TARGET)
run-test:
	$(NUNIT_CONSOLE) $(TEST_TARGET)

$(TARGET): $(SRC)
	$(MONO_CC) -out:$@  -t:library -unsafe+ $^

$(TEST_TARGET): $(TEST_SRC)
	$(MONO_CC) -out:$@  -t:library -r:$(TARGET) -r:nunit.framework.dll $^
