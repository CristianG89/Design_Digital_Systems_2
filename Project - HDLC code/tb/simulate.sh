#!/bin/bash

RED='\033[0;31m'
NC='\033[0m'

rm -rf transcript 

if ./compile.sh		#Compilation bash file is called to compile the whole design + verification files (command "vlog") before simulating
then
	echo "Success"
else
	echo "Failure"
	exit 1
fi

printf "${RED}\nSimulating${NC}\n"
if [[ "$@" =~ --gui ]]
then
	echo vsim -assertdebug -voptargs="+acc" test_hdlc bind_hdlc -do "log -r *" &
	exit
else
	if vsim -assertdebug -c -voptargs="+acc" test_hdlc bind_hdlc -do "log -r *; run -all;
		coverage report -memory -cvg -details -file coverage_report.txt; exit"		#This line has been added to apply coverage and generate report file
	then
		echo "Success"
	else
		echo "Failure"
		exit 1
	fi
fi
