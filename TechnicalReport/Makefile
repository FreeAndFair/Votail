export BIBINPUTS=.:../bibliography/:../../bibliography/:
export TEXINPUTS=.:../srgpapers/common//:

F:= report

.PHONY:	build clean html view pdflatex

all:	build

build:	${F}.pdf

${F}.pdf ${F}.bbl: ${F}.tex ${F}.bib
	rubber -W all --pdf ${F}.tex

clean:
	rubber --clean --pdf ${F} && rm -rf ${F}

html:	${F}/${F}.html

${F}/${F}.html: ${F}.tex ${F}.bib
	latex2html -split 0 ${F}

view:	${F}.pdf
	open -a Skim.app ${F}.pdf

pdflatex: 
	pdflatex ${F}
