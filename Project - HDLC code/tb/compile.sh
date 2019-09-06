rm -rf work*

RED='\033[0;31m'
NC='\033[0m'    

vlib work 

printf "${RED}\nCompiling design${NC}\n"		#DESIGN (RTL) FILES!!!!!!!!!!!!!
if vlog -sv ../rtl/*.sv		#This statement takes and compiles every single Verilog file with extension .sv, located in "../rtl/"
then
	echo "Success"
else
	echo "Failure"
	exit 1
fi

printf "${RED}\nCompiling test files${NC}\n"	#VERIFICATION (TESTBENCH) FILES!!!!!!!!!!!!!!
if vlog -sv ./*.sv			#This statement takes and compiles every single Verilog file with extension .sv, located in the local folder
then
	echo "Success"
else
	echo "Failure"
	exit 1
fi
