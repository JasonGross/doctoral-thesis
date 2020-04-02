# Print shell commands (set to non empty)
VERBOSE ?=

# Time the Coq process (set to non empty), and how (see default value)
TIMED?=
TIMECMD?=
# Use command time on linux, gtime on Mac OS
TIMEFMT?="$@ (real: %e, user: %U, sys: %S, mem: %M ko)"
ifneq (,$(TIMED))
ifeq (0,$(shell command time -f $(TIMEFMT) true >/dev/null 2>/dev/null; echo $$?))
STDTIME?=command time -f $(TIMEFMT)
else
ifeq (0,$(shell gtime -f $(TIMEFMT) true >/dev/null 2>/dev/null; echo $$?))
STDTIME?=gtime -f $(TIMEFMT)
else
STDTIME?=command time
endif
endif
else
STDTIME?=command time -f $(TIMEFMT)
endif

SHOW := $(if $(VERBOSE),@true "",@echo "")
HIDE := $(if $(VERBOSE),,@)

.PHONY: all clean cleanall
all:

SORT_COQPROJECT = sed 's,[^/]*/,~&,g' | env LC_COLLATE=C sort | sed 's,~,,g' | uniq
.PHONY: update-_CoqProject
update-_CoqProject:
	$(SHOW)'ECHO > _CoqProject'
	$(HIDE)(echo '-R . PerformanceExperiments'; (git ls-files "*.v" | $(SORT_COQPROJECT))) > _CoqProject

COQ_VERSION_FILE = .coq-version
COQ_VERSION_SHORT_FILE = .coq-version-short
COQ_VERSION_COMPILATION_DATE_FILE = .coq-version-compilation-date
COQ_VERSION_SHORT_DATE_FILE = .coq-version-short-date
COQ_VERSION_OCAML_VERSION_FILE = .coq-version-ocaml-version
COQ_VERSION_PREFIX = The Coq Proof Assistant, version
COQ_VERSION_FULL := $(subst $(COQ_VERSION_PREFIX),,$(shell $(COQBIN)coqc --version 2>/dev/null))
COQ_VERSION := $(firstword $(COQ_VERSION_FULL))
OPEN_PAREN:=(
CLOSE_PAREN:=)
EMPTY:=
SPACE:=$(EMPTY) $(EMPTY)
JOINER:=|
COQ_VERSION_DATE := $(subst $(OPEN_PAREN),,$(subst $(CLOSE_PAREN),,$(wordlist 2, 3, $(COQ_VERSION_FULL))))
COQ_VERSION_COMPILATION := $(subst $(JOINER)with,$(SPACE)with,$(subst $(SPACE),$(JOINER),$(wordlist 4, $(words $(COQ_VERSION_FULL)),$(COQ_VERSION_FULL))))
COQ_VERSION_COMPILATION_DATE := $(subst $(JOINER),$(SPACE),$(subst compiled$(JOINER)on$(JOINER),,$(firstword $(COQ_VERSION_COMPILATION))))
COQ_VERSION_COMPILATION_OCAML_VERSION := $(subst $(JOINER),$(SPACE),$(subst OCaml$(JOINER),,$(subst with$(JOINER),,$(word 2,$(COQ_VERSION_COMPILATION)))))

COQ_EXTENDED_VERSION := $(shell (true | $(COQBIN)coqtop 2>/dev/null; $(COQBIN)coqc --version 2>/dev/null))
COQ_EXTENDED_VERSION_OLD := $(shell cat $(COQ_VERSION_FILE) 2>/dev/null)

clean::
	rm -f $(COQ_VERSION_FILE) $(COQ_VERSION_SHORT_FILE) $(COQ_VERSION_SHORT_DATE_FILE) $(COQ_VERSION_COMPILATION_DATE_FILE) $(COQ_VERSION_OCAML_VERSION_FILE)

all: $(COQ_VERSION_FILE) $(COQ_VERSION_SHORT_FILE) $(COQ_VERSION_SHORT_DATE_FILE) $(COQ_VERSION_COMPILATION_DATE_FILE) $(COQ_VERSION_OCAML_VERSION_FILE)

ifneq ($(COQ_EXTENDED_VERSION),$(COQ_EXTENDED_VERSION_OLD))
.PHONY: $(COQ_VERSION_FILE) $(COQ_VERSION_SHORT_FILE) $(COQ_VERSION_SHORT_DATE_FILE) $(COQ_VERSION_COMPILATION_DATE_FILE) $(COQ_VERSION_OCAML_VERSION_FILE)

$(COQ_VERSION_FILE):
	$(SHOW)'echo $$COQ_VERSION_INFO ($(COQ_VERSION)) > $@'
	$(HIDE)echo "$(COQ_EXTENDED_VERSION)" > $@

$(COQ_VERSION_SHORT_FILE):
	$(SHOW)'echo $$COQ_VERSION_INFO ($(COQ_VERSION)) > $@'
	$(HIDE)echo "$(COQ_VERSION)" > $@

$(COQ_VERSION_SHORT_DATE_FILE):
	$(SHOW)'echo $$COQ_VERSION_INFO ($(COQ_VERSION), $(COQ_VERSION_DATE)) > $@'
	$(HIDE)echo "$(COQ_VERSION_DATE)" > $@

$(COQ_VERSION_COMPILATION_DATE_FILE):
	$(SHOW)'echo $$COQ_VERSION_INFO ($(COQ_VERSION), $(COQ_VERSION_COMPILATION_DATE)) > $@'
	$(HIDE)echo "$(COQ_VERSION_COMPILATION_DATE)" > $@

$(COQ_VERSION_COMPILATION_OCAML_VERSION_FILE):
	$(SHOW)'echo $$COQ_VERSION_INFO ($(COQ_VERSION), $(COQ_VERSION_COMPILATION_OCAML_VERSION)) > $@'
	$(HIDE)echo "$(COQ_VERSION_COMPILATION_OCAML_VERSION)" > $@
endif
