#!/bin/csh -fx
\rm -rf work
\rm test_counter_check2.log

vlib work

#--------------------------------------------------
#To compile with RTL that fails on Check 2
#--------------------------------------------------
vlog -sv counter.v counter_property.sv test_counter.sv +define+check2

#Simulate
vsim -assertdebug -coverage -c test_counter -l test_counter_check2.log -do " run -all; quit"
