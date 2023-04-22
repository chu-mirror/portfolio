COQMFFLAGS =  -Q . ProvedDES
VERIFIED = verified.v
ALLVFILES = ${VERIFIED}
trash = Makefile.coq Makefile.coq.conf

.SUFFIXES: .c .v
.c.v:
	clightgen -normalize $<

build: Makefile.coq ${VERIFIED}
	make -f Makefile.coq

cleanlocal: Makefile.coq
	make -f Makefile.coq cleanall

Makefile.coq:
	coq_makefile ${COQMFFLAGS} -o Makefile.coq ${ALLVFILES}


