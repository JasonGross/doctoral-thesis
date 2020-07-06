.DEFAULT_GOAL := all

_CoqProject: ;

Makefile.coq: _CoqProject
	$(COQBIN)coq_makefile -f $< -o $@

%: Makefile.coq
	$(MAKE) -f Makefile.coq $@
