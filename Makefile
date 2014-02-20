
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
		term-equivalence.tex \
		high-level-complete.tex \
		matching-continuations-aggregates.tex \
		ll-system/match-body.tex \
		ll-system/match-aggregate.tex \
		ll-system/aggregate-cont.tex \
		ll-system/comprehension-stack.tex \
		ll-system/comprehension-derivation.tex \
		ll-system/aggregate-stack.tex
	pdflatex doc.tex
	pdflatex doc.tex

clean:
	rm -f doc.pdf doc.aux doc.log
