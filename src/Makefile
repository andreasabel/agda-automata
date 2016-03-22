
destdir=$(HOME)/public_html

pdflatex=pdflatex -shell-escape -halt-on-error
bibtool=bibtool -- 'preserve.key.case = ON' \
	  -- 'check.double = ON' \
	  -- 'check.double.delete = ON' \
	  -- 'delete.field = { abstract }' \
	  -- 'delete.field = { dvi }' \
	  -- 'delete.field = { postscript }' \
	  -- 'delete.field = { pdf }' \
	  -- 'delete.field = { month }' \
	  -- 'delete.field = { isbn }'
#	  -- 'delete.field = { note }'
#	  -- 'delete.field = { editor }'
#	  -- 'delete.field = { doi }'

bibliography=all.bib
sedfile=postprocess.sed
stylefile=agda.sty
#stdlib=$(HOME)/agda-master/std-lib/src

allfiles=cmcs16.tex $(files)
files=postprocess.sed Makefile \
  macros.tex $(bibliography)


default : cmcs16.pdf

pack : cmcs16.zip

cmcs16.zip : cmcs16.tex llncs.cls splncsnat.bst macros.tex auto-cmcs16.bib
	zip $@ $^

# cmcs16
##################################################################

# initially, run latex once to create an .aux file
# mark .aux file as fresh by creating a stamp _aux
# note: -shell-escape essential for minted syntax highlighting
cmcs16_aux : cmcs16.tex $(files)
	$(pdflatex) cmcs16.tex;
	touch $@;

# then, run bibtex
cmcs16.bbl : cmcs16_aux auto-cmcs16.bib
	-bibtex cmcs16;

# finally, finish by running latex twice again
# this will update .aux, but leave the stamp _aux intact
# (otherwise we would not converge and make would never
# return a "Nothing to do")
cmcs16.pdf : cmcs16.bbl
	$(pdflatex) cmcs16.tex;
	$(pdflatex) cmcs16.tex;

# auto-cmcs16.bib is only defined if bibtool is present
# and $(bibliography) exists

ifneq ($(shell which bibtool),)
ifneq ($(shell ls $(bibliography)),)
auto-cmcs16.bib : cmcs16_aux $(bibliography)
	echo "%%%% WARNING! AUTOMATICALLY CREATED BIBFILE" > $@;
	echo "%%%% DO NOT EDIT! ALL CHANGES WILL BE LOST!" >> $@ ;
	echo "" >> $@ ;
	$(bibtool) -x cmcs16.aux -i $(bibliography) >> $@;
endif
endif


# Templates
##################################################################

latex/%.tex : %.lagda
	agda -i. -i$(agda_iolibnew) -i$(agda_stdlib) --latex $<

%.tex : latex/%.tex
	sed --file=$(sedfile) < $< > $@


# EOF
