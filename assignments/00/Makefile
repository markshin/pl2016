PFILES = $(shell find P??.v)
EFILES = $(shell find E??.v)

POFILES = $(patsubst %.v,%.vo,$(PFILES))
EOFILES = $(patsubst %.v,%.vo,$(EFILES))

pfiles: $(PFILES) Makefile.coq
	$(MAKE) -f Makefile.coq $(POFILES)

efiles: $(PFILES) $(EFILES) Makefile.coq
	$(MAKE) -f Makefile.coq $(EOFILES)

%.vo: Makefile.coq
	$(MAKE) -f Makefile.coq "$@"

clean: Makefile.coq
	$(MAKE) -f Makefile.coq clean
	rm _CoqProject Makefile.coq

Makefile.coq: Makefile $(PFILES) $(EFILES)
	(echo "-I ."; \
         echo $(PFILES) $(EFILES)) > _CoqProject
	coq_makefile -f _CoqProject -o Makefile.coq
