#!/bin/csh -f

if ($#argv != 1) then
    echo "Usage: $0 num, where num is check number"
    exit
endif

set max=5
set num=$argv[1]
if ($num > $max) then
    echo "Usage: $0 num, where num is check number 1 to $max"
    exit
endif

set fname=top_level
set top=test_top_level

set echo=1

## \rm -rf work
\rm -f test-${fname}-check${num}.log

if (! -d work) then
    vlib work
endif

vcom alu.vhd    #To include VHDL used in the Verilog file!!!!!!!!

#--------------------------------------------------
#To compile with RTL that fails on Check 1
#--------------------------------------------------
vlog -sv ${fname}.v ${fname}-property.sv test-${fname}.sv +acc +cover +define+check${num}

#Simulate
vsim -assertdebug -coverage -c $top -l test-${fname}-check${num}.log -do " run -all; quit"
