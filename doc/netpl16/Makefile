BibDir     = 
LaTeXEnv   = TEXINPUTS=.:${TEXINPUTS}:
BibTexEnv  = BIBINPUTS=.:${BibDir}:${BIBINPUTS}:

OutDir     = .

LaTeX      = ${LaTeXEnv} pdflatex
BibTeX     = ${BibTexEnv} bibtex
Ps2Pdf	   = ps2pdf
Dia2Eps    = dia -t eps -e
Eps2Pdf	   = epstopdf
mv	   = mv
awk	   = awk
Inkscape   = inkscape
Haskell    = runhaskell

# CONFIGURATION OPTIONS
# =====================

# Write the tex file name here
Target = paper

# List figures generated from .fig and .svg sources in the converted form that is
# sourced into LaTeX: either name1.pstex name1.pstex_t name2.pstex name2.pstex_t
# or name1.eps name2.eps ...  Mixtures are fine.
FigFiles = 

# Any other stuff that may be needed

# END CONFIGURATION OPTIONS


# Don't force a printer on people, use your own PRINTER environment!
#PRINTER = early@score
LPR = lpr

all: ${OutDir}/${Target}.pdf ${Target}.bbl

pdf: ${OutDir}/${Target}.pdf

view: ${Target}.pdf
	gv ${Target}.pdf &

print: ${Target}.pdf
	${LPR} -P${PRINTER} $<

clean:
	rm -f *.aux *.toc *.bbl *.bbl~ *.blg *.dvi *.log *.pstex* *.cb *.brf *.out 

realclean: clean
	rm -f *~ *.ps *.pdf *.tgz

tar:	realclean
	( p=`pwd` && d=`basename "$$p"` && cd .. && \
	  tar cfz $$d.tgz $$d && \
	  mv $$d.tgz $$d )

${Target}.toc: Makefile ${Target}.tex ${FigFiles}

%.svg: %.hs
	${Haskell} $< -o $@

%.pdf: %.eps
	${Eps2Pdf} $<

%.eps: %.dia
	${Dia2Eps} $@ $<

%.pdf: %.svg
	${Inkscape} --export-pdf=$@  $< 

%.pdf: %.dot
	dot $< -Tpdf -o $@

%.pdf: %.toc
	${LaTeX} $(patsubst %.toc,%,$<)

%.toc: %.bbl
	${LaTeX} $(patsubst %.bbl,%,$<)

%.bbl: %.tex ${FigFiles} Makefile
	${LaTeX} $(patsubst %.tex,%,$<)
#	${BibTeX} $(patsubst %.tex,%,$<)
## 	Fix BibTeX-generated line breaks that \url doesn't handle correctly:
#	${mv} $(patsubst %.tex,%,$<).bbl $(patsubst %.tex,%,$<).bbl~
#	${awk} <$(patsubst %.tex,%,$<).bbl~ >$(patsubst %.tex,%,$<).bbl \
#		'/%$$/{printf "%s", substr($$0,1,length()-1); next};{print}'
