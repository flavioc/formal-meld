
all: doc.pdf

doc.pdf: doc.tex
	pdflatex doc.tex
