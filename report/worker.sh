#!/bin/bash
# Escravo para limpar e construir coisas por mim
# Renato Neves

while getopts "cb" opt; do
	
	case $opt in

	c)  	echo "I will clean the folder for you :)";
	    	rm *.aux  *.log *.out;;

	b)  	echo "I will build the tex file and open it for you :)";
	  	pdflatex report && open report.pdf ;; 	
	\?) echo "wrong options" ;;
	
	esac
done
