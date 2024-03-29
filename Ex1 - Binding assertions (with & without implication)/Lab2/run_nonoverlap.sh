#!/bin/csh -fx
\rm -rf work
\rm test_nonoverlap.log


vlib work

#--------------------------------------------------
#To compile with nonoverlap implication
#--------------------------------------------------
vlog -sv test_overlap_nonoverlap.sv +define+nonoverlap


#Simulate
vsim -assertdebug -coverage -c test_overlap_nonoverlap -l test_nonoverlap.log -do "run -all; quit"
