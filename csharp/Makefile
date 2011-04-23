TARGET=MsgPack.dll
TEST_TARGET=MsgPack.Test.dll

SRC=$(shell find MsgPack -name "*.cs")
TEST_SRC=$(shell find MsgPack.Test -name "*.cs")

MONO_CC=mcs
NUNIT_CONSOLE=nunit-console

all: $(TARGET)
test: $(TEST_TARGET) $(TARGET)
clean:
	rm -f $(TARGET) $(TEST_TARGET)
run-test:
	$(NUNIT_CONSOLE) $(TEST_TARGET)

$(TARGET): $(SRC)
	$(MONO_CC) -out:$@  -t:library -unsafe+ $(SRC)

$(TEST_TARGET): $(TEST_SRC) $(TARGET)
	$(MONO_CC) -out:$@  -t:library -r:$(TARGET) -r:nunit.framework.dll $(TEST_SRC)
