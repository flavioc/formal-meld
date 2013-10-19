
all: doc.pdf

doc.pdf: doc.tex high-level.tex high-level-simple.tex \
		static.tex basic-with-compr.tex \
		dynamic-expressions.tex \
		matching-continuations.tex \
		matching-continuations-compr.tex \
		low-level-semantics.tex \
		global-semantics.tex local-semantics.tex \
		linear-logic.tex ideas.tex \
		matching-continuations-persistent.tex \
		high-level-persistent.tex \
		term-equivalence.tex
	pdflatex doc.tex
	pdflatex doc.tex

clean:
	rm -f doc.pdf doc.aux doc.log
