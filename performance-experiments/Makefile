# Forward most targets to Coq makefile (with some trick to make this phony)
%: Makefile.coq phony
	@$(MAKE) --no-print-directory -f Makefile.coq $@

.PHONY: all clean cleanall
all:: Makefile.coq
	@$(MAKE) --no-print-directory -f Makefile.coq all

include Makefile.characters
include Makefile.timing
include Makefile.coq-versions
include Makefile.variables

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq
.PHONY: update-_CoqProject
update-_CoqProject:
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R . $(PERF_LIB)'; (git ls-files "*.v" | $(SORT_COQPROJECT))) > _CoqProject

Makefile.coq: _CoqProject Makefile
	"$(COQBIN)coq_makefile" -f _CoqProject -o Makefile.coq

cleanall clean:: Makefile.coq
	$(MAKE) -f Makefile.coq $@
	rm -f Makefile.coq Makefile.coq.conf

# Some files that do *not* need to be forwarded to Makefile.coq
Makefile: ;
_CoqProject: ;
Makefile.variables: ;
Makefile.characters: ;
Makefile.coq-versions: ;
Makefile.timing: ;

# Phony wildcard targets
phony: ;
.PHONY: phony
