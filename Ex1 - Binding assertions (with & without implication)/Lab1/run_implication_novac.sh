#!/bin/csh -fx

\rm -rf work
\rm test_dut_implication_novac.log

vlib work

#--------------------------------------------------
#To compile with implication and no vaccuos pass
#--------------------------------------------------
vlog -sv dut.v dut_property.sv test_dut.sv +define+implication_novac

#Simulate
vsim -assertdebug -coverage -c test_dut -l test_dut_implication_novac.log -do "run -all; quit"