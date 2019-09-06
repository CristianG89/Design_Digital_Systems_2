#!/bin/csh -fx
\rm -rf work
\rm test_fifo_check3.log

#=======================================
# C R E A T E / S E T  'work' lib
#--------------------------------
vlib work

#--------------------------------------------------
# To compile with bug in RTL that is caught by CHECK # 3
# CHECK # 3. Check that fifo_full is asserted any time fifo 'cnt' is greater than 7.
# Disable this property 'iff (!rst)'
#--------------------------------------------------
vlog -sv fifo.v fifo_property.sv test_fifo.sv +define+check3

#--------------------------------------------------
#To Simulate
#--------------------------------------------------
vsim -assertdebug -coverage -c test_fifo -l test_fifo_check3.log -do " run -all; quit"
