include $(GOROOT)/src/Make.$(GOARCH)

TARG=msgpack

GOFILES=pack.go unpack.go

include $(GOROOT)/src/Make.pkg

%: install %.go
	$(GC) $*.go
	$(LD) -o $@ $*.$O
