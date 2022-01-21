all:
	agda --latex summary.lagda.tex
	latexmk -pdf --synctex=1 -interaction=nonstopmode  -file-line-error  latex/summary.tex
