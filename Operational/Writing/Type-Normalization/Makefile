DOC=TN
BIBFILE=bibliography
PDF=${DOC}.pdf
BIB=${BIBFILE}.bib

LAGDA = ${DOC}.lagda
SRC = ${DOC}.tex ${BIB} 

AGDA = agda --latex --latex-dir .
LATEX = pdflatex -halt-on-error -shell-escape # To get pstricks to work with PDF
BIBTEX = bibtex

#----------------------------------------------------------------

all: agda pdf bib pdf pdf

agda: 
	agda --latex --latex-dir . ${LAGDA}

bib : 
	bibtex ${DOC}
pdf:  
	${LATEX} ${DOC}


#----------------------------------------------------------------

clean:
	rm -f ${DOC}.tex *.aux *.log *.cov *.par *.bbl *.fls *.blg *.xml *.bcf *.dvi *.out *~
