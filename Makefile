COQTHEORIES  := $(shell find . -not -path "./deprecated/*" -not -path "./_opam/*" -iname '*.v')

%.vo: %.v
	$(MAKE) -f Makefile.coq $@

%.vos: %.v
	$(MAKE) -f Makefile.coq $@

all: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(COQTHEORIES))
all-quick: Makefile.coq $(COQTHEORIES)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(COQTHEORIES))
.PHONY: all all-quick

theories_files  := $(shell find theories -iname '*.v')
theories: Makefile.coq $(theories_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(theories_files))
theories-quick: Makefile.coq $(theories_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(theories_files))
.PHONY: theories theories-quick

formalizing_files := $(shell find formalizing -iname '*.v')
formalizing: Makefile.coq $(formalizing_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(formalizing_files))
formalizing-quick: Makefile.coq $(formalizing_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(formalizing_files))
.PHONY: formalizing formalizing-quick

stlc_files := $(shell find formalizing/Stlc -iname '*.v')
stlc: Makefile.coq $(stlc_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(stlc_files))
stlc-quick: Makefile.coq $(stlc_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(stlc_files))
.PHONY: stlc stlc-quick

stlcmore_files := $(shell find formalizing/StlcMore -iname '*.v')
stlcmore: Makefile.coq $(stlcmore_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(stlcmore_files))
stlcmore-quick: Makefile.coq $(stlcmore_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(stlcmore_files))
.PHONY: stlcmore stlcmore-quick

systemf_files := $(shell find formalizing/SystemF -iname '*.v')
systemf: Makefile.coq $(systemf_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vo,$(systemf_files))
systemf-quick: Makefile.coq $(systemf_files)
	$(MAKE) -f Makefile.coq $(patsubst %.v,%.vos,$(systemf_files))
.PHONY: systemf systemf-quick

Makefile.coq: Makefile $(COQTHEORIES)
	(echo "-arg -w -arg -deprecated-hint-without-locality"; \
	 echo "-arg -w -arg -deprecated-instance-without-locality"; \
	 echo "-arg -w -arg -notation-incompatible-prefix"; \
	 echo "-arg -w -arg -notation-overriden"; \
	 echo "-arg -w -arg -ambiguous-paths"; \
	 echo "-arg -w -arg -redundant-canonical-projection"; \
	 echo "-arg -w -arg -cannot-define-projection"; \
	 echo "-R theories Intro2TT"; \
	 echo "-R formalizing Formalizing"; \
	 echo $(COQTHEORIES)) > _CoqProject
	$(COQBIN)coq_makefile -f _CoqProject -o Makefile.coq
.PHONY: Makefile.coq

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean || true
	@# Make sure not to enter the `_opam` folder.
	find [a-z]*/ \( -name "*.d" -o -name "*.vo" -o -name "*.vo[sk]" -o -name "*.aux" -o -name "*.cache" -o -name "*.glob" -o -name "*.vos" \) -print -delete || true
	rm -f _CoqProject Makefile.coq Makefile.coq.conf .lia.cache .nia.cache
.PHONY: clean