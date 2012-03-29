#!/bin/bash
# Escravo para limpar e construir coisas por mim
# Renato

while getopts "cb" opt; do
	
	case $opt in

	c)  	echo "I will clean the folder for you :)";
	    	rm *.lps *.lts *.pbes *.aux  *.log *.out;;

	b)  	echo "I will build the tex file and open it for you :)";
	  	pdflatex report && open report.pdf ;; 	
	\?) echo "wrong options" ;;
	
	esac
done
