#!/bin/csh -fx
\rm -rf work
\rm test_fifo_check4.log

#=======================================
# C R E A T E / S E T  'work' lib
#--------------------------------
vlib work

#--------------------------------------------------
# To compile with bug in RTL that is caught by CHECK # 4
# CHECK #4. Check that if fifo is full and you attempt to write (but not read) that
# the wr_ptr does not change.
#--------------------------------------------------
vlog -sv fifo.v fifo_property.sv test_fifo.sv +define+check4

#--------------------------------------------------
#To Simulate
#--------------------------------------------------
vsim -assertdebug -coverage -c test_fifo -l test_fifo_check4.log -do "run -all; quit"
