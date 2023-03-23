# This file was automatically generated - modify ../Makefile.template instead
# Makefile originally taken from coq-club

%: Makefile.coq phony
	+make -f Makefile.coq $@

all: gen-coq-project Makefile.coq
	+make -f Makefile.coq all

clean: Makefile.coq
	+make -f Makefile.coq clean
	rm -f Makefile.coq

Makefile.coq: _CoqProject Makefile
	coq_makefile -f _CoqProject | sed 's/$$(COQCHK) $$(COQCHKFLAGS) $$(COQLIBS)/$$(COQCHK) $$(COQCHKFLAGS) $$(subst -Q,-R,$$(COQLIBS))/' > Makefile.coq

.PHONY: gen-coq-project
gen-coq-project:
	rm -f _CoqProject
	echo "# This file was automatically generated - see Makefile" >> _CoqProject
	cat _CoqProject.template >> _CoqProject
	echo $(wildcard *.v) >> _CoqProject # List the .v files
	sed -i -z "s/"$*"\//\n/g" _CoqProject # Insert breaks
	sed -i -z "s/ \n/\n/g" _CoqProject # Remove whitespaces at the end of lines
	cat _CoqProject

_CoqProject: ;

Makefile: ;

phony: ;

.PHONY: all clean phony
