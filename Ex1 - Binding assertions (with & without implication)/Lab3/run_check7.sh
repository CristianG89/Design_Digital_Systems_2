#!/bin/csh -fx
\rm -rf work
\rm test_fifo_check7.log

#=======================================
# C R E A T E / S E T  'work' lib
#--------------------------------
vlib work

#--------------------------------------------------
# To compile with bug in RTL that is caught by CHECK # 7
# CHECK #7. Write a property to Warn on write to a full fifo
#
# Note that this when this checker is fired, only a Warning is issued.
#--------------------------------------------------
vlog -sv fifo.v fifo_property.sv test_fifo.sv +define+check7

#--------------------------------------------------
#To Simulate
#--------------------------------------------------
vsim -assertdebug -coverage -c test_fifo -l test_fifo_check7.log -do " run -all; quit"
