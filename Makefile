.PHONY: all proposal thesis update-thesis update-proposal print-main-contents download-packages todo
all: proposal thesis

LATEXFLAGS?=--synctex=1 --shell-escape
PDFLATEX?=lualatex
MD5?=md5sum
OTHERFLAGS?=

READER_AGREEMENT_PDFS := \
	jgross-reader-agreement-unsigned.pdf adamc-reader-agreement-unsigned.pdf nickolai-reader-agreement-unsigned.pdf saman-reader-agreement-unsigned.pdf
MAIN_PROPOSAL_PDFS := jgross-thesis-proposal.pdf jgross-thesis-proposal-signed.pdf
PROPOSAL_PDFS = $(MAIN_PROPOSAL_PDFS) $(READER_AGREEMENT_PDFS)
THESIS_PDFS = jgross-thesis.pdf
MAIN_TEXS = $(patsubst \include{%},%.tex,$(filter \include{%},$(shell cat appendix-files.tex main-files.tex jgross-thesis.tex)))
THESIS_TEXS = packages.tex contents.tex mitthesis.cls abstract.tex cover.tex new-date.tex todo.tex main-files.tex appendix-files.tex $(MAIN_TEXS)
PROPOSAL_TEXS = new-date-proposal.tex abstract-proposal.tex
READER_AGREEMENT_SIGNED_PDFS := $(subst unsigned,signed,$(READER_AGREEMENT_PDFS))
PDFS = $(PROPOSAL_PDFS) $(THESIS_PDFS)

export TEXMFCNF=.:

OBERDIEK = accsupp aliascnt alphalph askinclude atbegshi atenddvi attachfile2 atveryend auxhook bigintcalc bitset bmpsize bookmark catchfile centernot chemarr classlist colonequals dvipscol embedfile engord enparen eolgrab epstopdf etexcmds fibnum flags gettitlestring grfext grffile hobsub hologo holtxdoc hopatch hycolor hypbmsec hypcap hypdestopt hypdoc hypgotoe hyphsubst ifdraft iflang ifluatex ifpdf ifvtex infwarerr inputenx intcalc kvdefinekeys kvoptions kvsetkeys letltxmacro listingsutf8 ltxcmds luacolor luatex magicnum makerobust mleftright pagegrid pagesel pdfcol pdfcolfoot pdfcolmk pdfcolparallel pdfcolparcolumns pdfcrypt pdfescape pdflscape pdfrender pdftexcmds picture pmboxdraw protecteddef refcount rerunfilecheck resizegather rotchiffre scrindex selinput setouterhbox settobox soulutf8 stackrel stampinclude stringenc tabularht tabularkv telprint thepdfnumber transparent twoopt uniquecounter zref
MATH = amsbsy  amscd  amsgen  amsmath  amsopn  amstext  amsxtra
TOOLS = afterpage array bm calc dcolumn delarray enumerate fileerr fontsmpl ftnright hhline indentfirst layout longtable multicol rawfonts showkeys somedefs tabularx theorem trace varioref verbatim xr xspace
TOOLS_IN = afterpage.dtx afterpage.ins array.dtx bm.dtx bm.ins calc.dtx dcolumn.dtx delarray.dtx enumerate.dtx fileerr.dtx fontsmpl.dtx ftnright.dtx hhline.dtx indentfirst.dtx layout.dtx longtable.dtx longtable.ins multicol.dtx multicol.ins rawfonts.dtx showkeys.dtx somedefs.dtx tabularx.dtx tabularx.ins theorem.dtx tools.ins trace.dtx varioref.dtx varioref.ins verbatim.dtx xr.dtx xspace.dtx

V = 0

Q_0 := @
Q_1 :=
Q = $(Q_$(V))
HIDE = $(Q)

VECHO_0 := @echo ""
VECHO_1 := @true ""
VECHO = $(VECHO_$(V))
SHOW = $(VECHO)

WGET_0 = @ echo "WGET $(1)"; wget --no-check-certificate -N $(2) 2>/dev/null
WGET_1 = wget --no-check-certificate -N $(2)
WGET = $(call WGET_$(V),$(1),$(2))

UNZIP_0 = unzip -qu
UNZIP_1 = unzip -u
UNZIP = $(UNZIP_$(V))

UNZIPJ_0 = unzip -quj
UNZIPJ_1 = unzip -uj
UNZIPJ = $(UNZIPJ_$(V))

print-main-contents::
	@ echo "$(MAIN_TEXS)"

proposal: $(PROPOSAL_PDFS)

thesis: $(THESIS_PDFS)

update-thesis::
	echo '\\thesisdate{'"`date +'%B %-d, %Y'`}" > new-date.tex
	$(MAKE) thesis

update-proposal::
	printf '\\newcommand{\\proposaldate}{%s}\n' "`date +'%B %-d, %Y'`" > new-date-proposal.tex
	$(MAKE) proposal

download-packages: mathtools.sty mhsetup.sty etoolbox.sty biblatex.sty logreq.sty

biblatex.zip mathtools.zip xcolor.zip oberdiek.zip cmap.zip hyperref.zip float.zip listings.zip microtype.zip::
	$(call WGET,$@,"http://mirrors.ctan.org/macros/latex/contrib/$@")

graphics.zip tools.zip::
	$(call WGET,$@,"http://mirrors.ctan.org/macros/latex/required/$@")

math.zip::
	$(call WGET,$@,"http://mirrors.ctan.org/macros/latex/required/amslatex/$@")

amsfonts.zip marvosym.zip::
	$(call WGET,$@,"http://mirrors.ctan.org/fonts/$@")

ifxetex.zip::
	$(call WGET,$@,"http://mirrors.ctan.org/macros/generic/$@")

mathtools/%: mathtools.zip
	$(UNZIP) $<

xcolor/%: xcolor.zip
	$(UNZIP) $<

graphics/%: graphics.zip
	$(UNZIP) $<

ifxetex/%: ifxetex.zip
	$(UNZIP) $<

oberdiek/%: oberdiek.zip
	$(UNZIP) $<

float/%: float.zip
	$(UNZIP) $<

biblatex/%: biblatex.zip
	$(UNZIP) $<

hyperref/%: hyperref.zip
	$(UNZIP) $<

math/%: math.zip
	$(UNZIP) $<

listings/%: listings.zip
	$(UNZIP) $<

marvosym/%: marvosym.zip
	$(UNZIP) $<

tools/%: tools.zip
	$(UNZIP) $<

microtype/%: microtype.zip
	$(UNZIP) $<

amsfonts/source/amssymb.def: amsfonts.zip
	$(UNZIP) $<

biblatex.sty: biblatex/latex/biblatex.sty
	find biblatex -name "*.sty" -o -name "*.bbx" -o -name "*.bst" -o -name "*.cbx" -o -name "*.cfg" -o -name "*.csf" -o -name "*.def" -o -name "*.lbx" | xargs cp -f -t ./

amssymb.def: amsfonts/source/amssymb.def
	cp -f amsfonts/source/*.{dtx,ins,tex,def,mf} amsfonts/afm/*.afm amsfonts/map/*.map amsfonts/pfb/*.{pfm,pfb} amsfonts/tfm/*.tfm ./

marvosym.sty: marvosym/tex/latex/marvosym.sty
	cp -f marvosym/tex/latex/marvosym/marvosym.sty marvosym/tex/latex/marvosym/*.fd marvosym/fonts/{afm,tfm,truetype,type1}/public/marvosym/* marvosym/fonts/map/dvips/marvosym/*.map ./

amsfonts.dtx amsfonts.ins: amssymb.def

cmap.sty: cmap.zip
	$(UNZIP) $<
	cp -f cmap/*.sty cmap/*.cmap ./

fontenc.sty t1enc.def ts1enc.def ts1cmr.fd size12.clo::
	$(call WGET,$@,"https://ctan.org/tex-archive/macros/latex/unpacked/$@")

supp-pdf.mkii supp-mis.mkii supp-mpe.mkii syst-tex.mkii::
	$(call WGET,$@,"http://mirrors.ctan.org/graphics/metapost/contrib/tools/mptopdf/tex/context/base/$@")

textcomp.sty knappen.mai TS1.etx TS1i.etx textcomp.dtx textcomp.ins::
	$(call WGET,$@,"http://mirrors.ctan.org/obsolete/fonts/psfonts/ts1/$@")

textcomp.sty:: knappen.mai TS1.etx TS1i.etx

pdftex.def::
	$(call WGET,$@,"https://ctan.org/tex-archive/macros/latex/contrib/pdftex-def/$@")

setspace.sty bussproofs.sty url.sty::
	$(call WGET,$@,"http://mirrors.ctan.org/macros/latex/contrib/$(patsubst %.sty,%,$@)/$@")

etoolbox.sty::
	$(call WGET,$@,"http://mirrors.ctan.org/macros/latex/contrib/$(patsubst %.sty,%,$@)/$@")
	$(call WGET,$@,"http://mirrors.ctan.org/macros/latex/contrib/$(patsubst %.sty,%,$@)/$(patsubst %.sty,%.def,$@)")
	$(call WGET,$@,"http://mirrors.ctan.org/macros/latex/contrib/$(patsubst %.sty,%,$@)/$(patsubst %.sty,%.tex,$@)")

logreq.sty::
	$(call WGET,$@,"http://mirrors.ctan.org/macros/latex/contrib/$(patsubst %.sty,%,$@)/$@")
	$(call WGET,$@,"http://mirrors.ctan.org/macros/latex/contrib/$(patsubst %.sty,%,$@)/$(patsubst %.sty,%.def,$@)")

mathtools.dtx mhsetup.dtx : % : mathtools/%
	cp -f $< $@

microtype.dtx microtype-utf.dtx microtype.ins : % : microtype/%
	cp -f $< $@

float.ins float.dtx : % : float/%
	cp -f $< $@

backref.dtx bmhydoc.sty hylatex.ltx hyperref.dtx hyperref.ins minitoc-hyper.sty nameref.dtx ntheorem-hyper.sty xr-hyper.sty : % : hyperref/%
	cp -f $< $@

xcolor.dtx xcolor.ins : % : xcolor/%
	cp -f $< $@

listings.dtx listings.ins lstdrvrs.dtx lstdrvrs.ins : % : listings/%
	cp -f $< $@

ifxetex.ins ifxetex.tex : % : ifxetex/%
	cp -f $< $@

color.dtx drivers.dtx epsfig.dtx graphics-drivers.ins graphics.dtx graphics.ins graphicx.dtx keyval.dtx lscape.dtx trig.dtx : % : graphics/%
	cp -f $< $@

$(addsuffix .dtx,$(OBERDIEK)) : % : oberdiek/%
	cp -f $< $@

$(TOOLS_IN) : % : tools/%
	cp -f $< $@

$(addsuffix .dtx,$(MATH)) $(addsuffix .ins,$(MATH)) : % : math/%
	cp -f $< $@

graphics.sty: color.dtx drivers.dtx epsfig.dtx graphics-drivers.ins graphics.dtx graphics.ins graphicx.dtx keyval.dtx lscape.dtx trig.dtx
	$(VECHO) LATEX graphics.ins
	latex graphics.ins

color.sty epsfig.sty graphics-drivers.ins graphicx.sty keyval.sty lscape.sty trig.sty: graphics.sty

$(addsuffix .sty,$(TOOLS)): tools.sty

tools.sty : %.sty : $(TOOLS_IN)
	$(VECHO) LATEX $*.ins
	yes "y" | latex $*.ins

mathtools.sty mhsetup.sty $(addsuffix .sty,$(OBERDIEK)) : %.sty : %.dtx
	$(VECHO) TEX $<
	tex $<

listings.sty: lstdrvrs.sty

lstmisc.sty lstlang1.sty lstlang2.sty: listings.sty

microtype.sty: microtype-utf.dtx

xcolor.sty $(addsuffix .sty,$(MATH)) float.sty listings.sty lstdrvrs.sty microtype.sty : %.sty : %.dtx %.ins
	$(VECHO) LATEX $*.ins
	latex $*.ins

ifxetex.sty : %.sty : %.tex %.ins
	$(VECHO) LATEX $*.ins
	latex $*.ins

amsfonts.sty : %.sty : amssymb.def
	$(VECHO) LATEX $*.ins
	latex $*.ins

amssymb.sty: amsfonts.sty

hyperref.sty : %.sty : backref.dtx bmhydoc.sty hylatex.ltx hyperref.dtx hyperref.ins minitoc-hyper.sty nameref.dtx ntheorem-hyper.sty xr-hyper.sty
	$(VECHO) LATEX $*.ins
	latex $*.ins

#mathtools/mathtools.dtx

#http://mirrors.ctan.org/macros/latex/contrib/mathtools.zip && unzip mathtools.zip && (cd mathtools && for i in *.dtx; do (mv $i ../ && cd .. && tex $i); done)

$(PDFS): jgross-thesis.bib

$(THESIS_PDFS): $(THESIS_TEXS)

$(PROPOSAL_PDFS): $(PROPOSAL_TEXS)

jgross-thesis-proposal-signed.pdf: jgross-thesis-proposal.tex $(READER_AGREEMENT_SIGNED_PDFS)
$(READER_AGREEMENT_PDFS): jgross-thesis-proposal.pdf

include rewriting/PerfData.mk
REWRITING_PERF_DATA_MD5 := $(addsuffix .md5,$(REWRITING_PERF_DATA))

include performance-experiments/Makefile.variables.kinds
EXPERIMENTS_PERF_DATA_MD5 := $(addprefix performance-experiments/,$(addsuffix .txt.md5,$(subst _,-,$(ALL_KINDS))))

include performance-experiments-8-9/Makefile.variables.kinds
EXPERIMENTS_PERF_DATA_MD5 += $(addprefix performance-experiments-8-9/,$(addsuffix .txt.md5,$(subst _,-,$(ALL_KINDS))))

$(THESIS_PDFS): $(REWRITING_PERF_DATA) $(REWRITING_PERF_DATA_MD5) $(EXPERIMENTS_PERF_DATA_MD5) rewriting/trust?.pdf

.PHONY: remake-rewriting-PerfData.mk
remake-rewriting-PerfData.mk:
	$(MAKE) -B rewriting/PerfData.mk

rewriting/PerfData.mk:
	(echo "REWRITING_PERF_DATA := \\"; (git ls-files "rewriting/perf-*.txt" | sed s'/\(.*\)/\t\1 \\/g' | sed s'/;/\\;/g'); printf '\t#\n') > $@

%.md5: %
	$(MD5) '$<' | awk '{print $$1}' > '$@'

%.pdf: %.tex.d

print-errors:
	$(HIDE)for i in jgross-thesis*-figure*.log; do \
	  echo '============================'; \
	  echo "$$i"; \
	  echo '============================'; \
	  cat "$$i"; \
	  echo '============================'; \
	done
	false
.PHONY: print-errors

$(MAIN_PROPOSAL_PDFS) $(THESIS_PDFS) : %.pdf : %.tex
	$(SHOW)"PDFLATEX (run 1)"
	$(HIDE)$(PDFLATEX) $(LATEXFLAGS) $(OTHERFLAGS) $< || $(MAKE) print-errors
	$(SHOW)"BIBER"
	$(HIDE)rm -f $*-biber.ok
	$(HIDE)(biber $* 2>&1 && touch $*-biber.ok) | tee $*-biber.log
	$(HIDE)rm $*-biber.ok
	$(SHOW)"PDFLATEX (run 2)"
	$(HIDE)$(PDFLATEX) $(LATEXFLAGS) $(OTHERFLAGS) --interaction=nonstopmode $< 2>&1 >/dev/null || true
	$(SHOW)"PDFLATEX (run 3)"
	$(HIDE)$(PDFLATEX) $(LATEXFLAGS) $(OTHERFLAGS) $< || $(MAKE) print-errors

$(READER_AGREEMENT_PDFS) : %.pdf : %.tex
	$(SHOW)"PDFLATEX"
	$(HIDE)$(PDFLATEX) $(LATEXFLAGS) $(OTHERFLAGS) $< || $(MAKE) print-errors

.PHONY: rubber
rubber:
	rubber --shell-escape -d -m lualatex jgross-thesis.tex

# pdflatex -synctex=1 -interaction=nonstopmode -enable-write18 jgross-thesis.tex 2>&1
.PHONY: todo
todo:
	etc/make-todo.sh

.PHONY: full-todo
full-todo:
	etc/make-full-todo.sh

todo.svg: jgross-thesis.pdf Makefile etc/make-todo.sh etc/makesvg.sh
	etc/make-todo.sh | etc/makesvg.sh > $@

full-todo.svg: jgross-thesis.pdf Makefile etc/make-full-todo.sh etc/makesvg.sh
	etc/make-full-todo.sh | etc/makesvg.sh > $@

.PHONY: deploy
deploy::
	mkdir -p deploy/nightly
	cp -f $(PDFS) todo.svg full-todo.svg deploy/nightly/

.PHONY: clean
clean:
	rm -f *.aux *.out *.nav *.toc *.vrb $(PDFS) *.snm *.log *.bbl *.blg *.tex.d *.run.xml *.atfi *.auxlock *.bcf *-blx.bib *.synctex.gz *'.synctex.gz(busy)' *.synctex *'.synctex(busy)'

# $ grep -v '^#' .gitignore  | grep -v '^$' | grep -v '^\*.pdf$' | sed 's/\(([^()]*)\)/'"'\1'"'/g; s,^/,./,g' | tr '\n' ' '; echo
.PHONY: cleanall
cleanall::
	rm -f $(PDFS)
	rm -rf *~ *\# .\#* *.atfi *.swp *.aux *.lof ./*.log *.lot *.fls *.out *.toc *.fmt *.fot *.cb *.cb2 .*.lb *.dvi *.xdv *-converted-to.* .pdf *.bbl *.bcf *.blg *-blx.aux *-blx.bib *.run.xml *.fdb_latexmk *.synctex *.synctex'(busy)' *.synctex.gz *.synctex.gz'(busy)' *.pdfsync *.alg *.loa acs-*.bib *.thm *.nav *.pre *.snm *.vrb *.soc *.cpt *.spl *.ent *.lox *.mf *.mp *.t[1-9] *.t[1-9][0-9] *.tfm *.end *.?end *.[1-9] *.[1-9][0-9] *.[1-9][0-9][0-9] *.[1-9]R *.[1-9][0-9]R *.[1-9][0-9][0-9]R *.eledsec[1-9] *.eledsec[1-9]R *.eledsec[1-9][0-9] *.eledsec[1-9][0-9]R *.eledsec[1-9][0-9][0-9] *.eledsec[1-9][0-9][0-9]R *.acn *.acr *.glg *.glo *.gls *.glsdefs *-gnuplottex-* *.gaux *.gtex *.4ct *.4tc *.idv *.lg *.trc *.xref *.brf *-concordance.tex *.tikz *-tikzDictionary *.lol *.idx *.ilg *.ind *.ist *.maf *.mlf *.mlt *.mtc[0-9]* *.slf[0-9]* *.slt[0-9]* *.stc[0-9]* _minted* *.pyg *.mw *.nlg *.nlo *.nls *.pax *.pdfpc *.sagetex.sage *.sagetex.py *.sagetex.scmd *.wrt *.sout *.sympy sympy-plots-for-*.tex/ *.upa *.upb *.pytxcode pythontex-files-*/ *.loe *.dpth *.md5 *.auxlock *.tdo *.lod *.xmpi *.xdy *.xyc *.ttt *.fff TSWLatexianTemp* *.bak *.sav .texpadtmp *.backup *~[0-9]* ./auto/* *.el *-tags.tex *.sta *.spl *.drv *.dtx *.ins *.bbx *.cbx *.lbx *.def *.cfg *.bst mathtools.sty mhsetup.sty mathtools.zip ./mathtools/ biblatex.sty biblatex.zip ./biblatex/ etoolbox.sty etoolbox.tex logreq.sty *.md5 ./todo.svg jgross-thesis*-figure*.dep *.pgf-plot.gnuplot *.pgf-plot.table *-parameters.dat [._]*.s[a-v][a-z] [._]*.sw[a-p] [._]s[a-v][a-z] [._]sw[a-p] *~ \#*\# ./.emacs.desktop ./.emacs.desktop.lock *.elc auto-save-list tramp .\#* *.pyc *.aux *.d *.glob *.vio *.vo *.vos *.vok CoqMakefile.conf Makefile.bak Makefile.coq Makefile.coq.conf Makefile.coq.bak Makefile-old.conf csdp.cache lia.cache nlia.cache nia.cache nra.cache .csdp.cache .lia.cache .nlia.cache .nia.cache .nra.cache *_SuperFast.v *_Fast.v *_Medium.v *_Slow.v *_VerySlow.v
