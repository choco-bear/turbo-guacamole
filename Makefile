all: Makefile.coq
	$(MAKE) -f Makefile.coq all

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq

install: Makefile.coq
	$(MAKE) -f Makefile.coq install

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean

cleanall: Makefile.coq
	$(MAKE) -f Makefile.coq cleanall

.PHONY: all install clean cleanall Makefile.coq