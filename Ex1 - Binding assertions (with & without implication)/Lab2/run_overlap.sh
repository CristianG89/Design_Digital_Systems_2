#!/bin/csh -fx
\rm -rf work
\rm test_overlap.log


vlib work

#--------------------------------------------------
#To compile with overlap implication
#--------------------------------------------------
vlog -sv test_overlap_nonoverlap.sv +define+overlap

#Simulate
vsim -assertdebug -coverage -c test_overlap_nonoverlap -l test_overlap.log -do "run -all; quit"
