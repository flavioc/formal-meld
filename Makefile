
all: doc.pdf

doc.pdf: doc.tex
	pdflatex doc.tex

clean:
	rm -f doc.pdf doc.aux doc.log
