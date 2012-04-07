#!/bin/bash
# Escravo para limpar e construir coisas por mim

while getopts "cb" opt; do
	
	case $opt in

	c)  	echo "I will clean the folder for you :)";
	    	rm *.aux  *.log *.out;;

	b)  	echo "I will build the tex file and open it for you :)";
			pdflatex report.tex && bibtex report && pdflatex report.tex &&
			pdflatex report.tex &&
			rm *.aux *.log *.out *.bbl *.blg  && open report.pdf ;; 	
	\?) echo "wrong options" ;;
	
	esac
done
