all:
	cp summary.tex summary.lagda.tex
	agda --subtyping --latex summary.lagda.tex
	latexmk -pdf --synctex=1 -interaction=nonstopmode  -file-line-error  latex/summary.tex
