#!/bin/csh -fx

\rm -rf ./work
\rm test_dut_implication.log

vlib work

#--------------------------------------------------
#To compile with implication
#--------------------------------------------------
vlog -sv dut.v dut_property.sv test_dut.sv +define+implication

#Simulate
vsim -assertdebug -coverage -c test_dut -l test_dut_implication.log -do "run -all; quit"