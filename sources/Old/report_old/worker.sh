#!/bin/bash
# Escravo para limpar e construir coisas por mim

while getopts "cb" opt; do
	
	case $opt in

	c)  	echo "I will clean the folder for you :)";
	    	rm *.aux  *.log *.out;;

	b)  	echo "I will build the tex file and open it for you :)";
			pdflatex report.tex && 
			makeglossaries report.glo &&
			makeindex report.glo -s report.ist -t report.glg -o report.gls &&
			bibtex report && pdflatex report.tex &&
			pdflatex report.tex &&
			rm *.aux *.log *.out *.bbl *.blg  *.gls *.glo *.ist *.glg && 
			open report.pdf ;; 	
	\?) echo "wrong options" ;;
	
	esac
done
