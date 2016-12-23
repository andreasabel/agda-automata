# Makefile for contnorm

destdir=$(HOME)/public_html

# commands
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }' \
	  -- 'delete.field = { doi }'
catcfg=sed -e "s/%.*//g" <
latex=latex
pdflatex=pdflatex
bibliography=all.bib
sedfile=postprocess.sed
stdlib=$(HOME)/agda-master/std-lib/src
agda=agda-2.5.2

stylefile=src/latex/agda.sty
files=$(bibliography) byhand.bib $(stylefile) macros.tex latex/Agda.tex latex/RewriteExample.tex latex/Language.tex latex/Automaton.tex

default : jlamp17.pdf

ship : $(destdir)/jlamp17.pdf

$(destdir)/jlamp17.pdf : jlamp17.pdf
	cp -p $< $@

$(destdir)/jlamp17a.lagda : jlamp17a.lagda
	cp -p $< $@

pack : jlamp17.zip

jlamp17.zip : jlamp17.tex jlamp17.bbl latex/agda.sty textgreek.sty # auto-jlamp17.bib byhand.bib eptcs.cls eptcs.bst
	zip $@ jlamp17.tex jlamp17.bbl latex/agda.sty textgreek.sty


# jlamp17
##################################################################

latex/%.tex : src/latex/%.tex $(sedfile)
	sed --file=$(sedfile) < $< > $@

src/latex/%.tex : src/%.lagda
	cd src; $(agda) --latex $*.lagda
#	agda --latex -i. -i$(stdlib) $<

# jlamp17.pdf : jlamp17a.lagda
#	pdflatex $<

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
jlamp17_aux : jlamp17.tex $(files)
	-$(pdflatex) jlamp17.tex;
	touch $@;

# then, run bibtex
jlamp17.bbl : jlamp17_aux auto-jlamp17.bib
	-bibtex jlamp17;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
jlamp17.pdf : jlamp17.bbl
	$(pdflatex) jlamp17.tex;
	$(pdflatex) jlamp17.tex;

# auto-jlamp17.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-jlamp17.bib : jlamp17_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x jlamp17.aux -i $(bibliography) >> $@;
endif
endif


# paper
##################################################################

paper.tex : latex/paper.tex
	sed -e 's/\\AgdaSymbol{\\{}\([a-zA-Z?]\+\) \\AgdaSymbol{=}/\\AgdaSymbol{\\{}\\AgdaSymbol{\1} \\AgdaSymbol{=}/' \
	  -e 's/\\AgdaFunction{≡⟨⟩}/\\AgdaFunction{\\qquad≡⟨⟩}/' \
	  -e 's/\\AgdaFunction{∼⟨}/\\AgdaFunction{\\qquad∼⟨}/' < $< > $@
#	sed -e 's/\\AgdaFunction{≡⟨⟩}/\\AgdaFunction{\\qquad≡⟨⟩}/' < $< > $@
#	sed -e 's/\\AgdaFunction{∼⟨}/\\AgdaFunction{\\qquad∼⟨}/' < $< > $@
#	sed -e 's/\\AgdaSymbol{\\{}a \\AgdaSymbol{=}/\\AgdaSymbol{\\{}\\AgdaSymbol{a} \\AgdaSymbol{=}/' -e 's/\\AgdaSymbol{\\{}u? \\AgdaSymbol{=}/\\AgdaSymbol{\\{}\\AgdaSymbol{u?} \\AgdaSymbol{=}/' < $< > $@

latex/paper.tex : paper.lagda
	agda --latex -i. -i$(stdlib) $<

# paper.pdf : paper.lagda
#	pdflatex $<

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
paper_aux : paper.tex $(files)
	$(pdflatex) paper.tex;
	touch $@;

# then, run bibtex
paper.bbl : paper_aux auto-paper.bib
	-bibtex paper;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
paper.pdf : paper.bbl
	$(pdflatex) paper.tex;
	$(pdflatex) paper.tex;

# auto-paper.bib is only defined if bibtool is present and all.bib exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-paper.bib : paper_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x paper.aux -i $(bibliography) >> $@;
endif
endif

# EOF
