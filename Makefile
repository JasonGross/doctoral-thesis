.PHONY: all proposal thesis update-thesis update-proposal print-main-contents download-packages todo
all: proposal thesis

PROPOSAL_PDFS = jgross-thesis-proposal.pdf
THESIS_PDFS = jgross-thesis.pdf
MAIN_TEXS = $(patsubst \include{%},%.tex,$(filter \include{%},$(shell cat main-files.tex jgross-thesis.tex)))
THESIS_TEXS = packages.tex contents.tex mitthesis.cls abstract.tex cover.tex new-date.tex todo.tex main-files.tex $(MAIN_TEXS)
PROPOSAL_TEXS = new-date-proposal.tex abstract-proposal.tex
PDFS = $(PROPOSAL_PDFS) $(THESIS_PDFS)

OBERDIEK = accsupp aliascnt alphalph askinclude atbegshi atenddvi attachfile2 atveryend auxhook bigintcalc bitset bmpsize bookmark catchfile centernot chemarr classlist colonequals dvipscol embedfile engord enparen eolgrab epstopdf etexcmds fibnum flags gettitlestring grfext grffile hobsub hologo holtxdoc hopatch hycolor hypbmsec hypcap hypdestopt hypdoc hypgotoe hyphsubst ifdraft iflang ifluatex ifpdf ifvtex infwarerr inputenx intcalc kvdefinekeys kvoptions kvsetkeys letltxmacro listingsutf8 ltxcmds luacolor luatex magicnum makerobust mleftright pagegrid pagesel pdfcol pdfcolfoot pdfcolmk pdfcolparallel pdfcolparcolumns pdfcrypt pdfescape pdflscape pdfrender pdftexcmds picture pmboxdraw protecteddef refcount rerunfilecheck resizegather rotchiffre scrindex selinput setouterhbox settobox soulutf8 stackrel stampinclude stringenc tabularht tabularkv telprint thepdfnumber transparent twoopt uniquecounter zref
MATH = amsbsy  amscd  amsgen  amsmath  amsopn  amstext  amsxtra
TOOLS = afterpage array bm calc dcolumn delarray enumerate fileerr fontsmpl ftnright hhline indentfirst layout longtable multicol rawfonts showkeys somedefs tabularx theorem trace varioref verbatim xr xspace
TOOLS_IN = afterpage.dtx afterpage.ins array.dtx bm.dtx bm.ins calc.dtx dcolumn.dtx delarray.dtx enumerate.dtx fileerr.dtx fontsmpl.dtx ftnright.dtx hhline.dtx indentfirst.dtx layout.dtx longtable.dtx longtable.ins multicol.dtx multicol.ins rawfonts.dtx showkeys.dtx somedefs.dtx tabularx.dtx tabularx.ins theorem.dtx tools.ins trace.dtx varioref.dtx varioref.ins verbatim.dtx xr.dtx xspace.dtx

V = 0

Q_0 := @
Q_1 :=
Q = $(Q_$(V))

VECHO_0 := @echo
VECHO_1 := @true
VECHO = $(VECHO_$(V))

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
	echo "\\thesisdate{`date +'%B %-d, %Y'`}" > new-date.tex
	$(MAKE) thesis

update-proposal::
	echo "\\\\newcommand{\\\\proposaldate}{`date +'%B %-d, %Y'`}" > new-date-proposal.tex
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

$(PDFS): references.bib

$(THESIS_PDFS): $(THESIS_TEXS)

$(PROPOSAL_PDFS): $(PROPOSAL_TEXS)

%.pdf: %.tex.d

$(THESIS_PDFS) : %.pdf : %.tex
	@ echo "PDFLATEX (run 1)"
	@ pdflatex -synctex=1 -enable-write18 $(OTHERFLAGS) $<
	@ echo "BIBTEX"
	@ bibtex ${<:.tex=.aux}
	@ echo "PDFLATEX (run 2)"
	@ pdflatex -synctex=1 -interaction=nonstopmode $(OTHERFLAGS) -enable-write18 $< 2>&1 >/dev/null || true
	@ echo "PDFLATEX (run 3)"
	@ pdflatex -synctex=1 $(OTHERFLAGS) $<

$(PROPOSAL_PDFS) : %.pdf : %.tex
	@ echo "PDFLATEX (run 1)"
	@ pdflatex -synctex=1 -enable-write18 $(OTHERFLAGS) $<
	@ echo "PDFLATEX (run 2)"
	@ pdflatex -synctex=1 -interaction=nonstopmode $(OTHERFLAGS) -enable-write18 $< 2>&1 >/dev/null || true
	@ echo "PDFLATEX (run 3)"
	@ pdflatex -synctex=1 $(OTHERFLAGS) $<

todo: jgross-thesis.pdf
	pdflatex -synctex=1 -interaction=nonstopmode -enable-write18 jgross-thesis.tex 2>&1 | grep -C 10 '^LaTeX Warning:\|on input line' | tr '\n' '&' | sed s'/\&//g' | sed s'/\(on input line[^\.]*\.\)/\1\&/g' | tr '&' '\n' | grep -o 'LaTeX Warning:.*' | grep -o 'TODO.*\|QUESTION.*' | grep --color=auto 'TODO:\|QUESTION FOR ADAM:'

clean:
	rm -f *.aux *.out *.nav *.toc *.vrb $(PDFS) *.snm *.log *.bbl *.blg *.tex.d *.run.xml
