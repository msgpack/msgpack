include $(GOROOT)/src/Make.inc

TARG=msgpack

GOFILES=pack.go unpack.go

include $(GOROOT)/src/Make.pkg

%: install %.go
	$(GC) $*.go
	$(LD) -o $@ $*.$O
