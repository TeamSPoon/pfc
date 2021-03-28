## This will normally have to be run twice when starting from scratch.
## Repetition of latex runs within each command does not always seem to work
## well with pdf hyperlinks, so it is better to have the warning from LaTeX.

all:	manual.dvi

install: manual.pdf
	cp manual.pdf ../../../doc

manual.dvi: *.tex manual.bbl
	latex manual
	makeindex  -s index_style.ist manual
	latex manual

manual.bbl: bibliography.bib
	latex manual
	bibtex manual

manual.pdf: manual.dvi
	pdflatex manual

clean:
	rm -rf *.aux *.log *.bbl *.blg *.idx *.ind *.ilg *.toc *.out

realclean: clean
	rm -rf manual.dvi manual.pdf
