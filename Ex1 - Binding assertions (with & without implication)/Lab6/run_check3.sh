#!/bin/csh -fx

\rm -rf work
\rm test_pci_protocol_check3.log

#=======================================
# C R E A T E / S E T  'work' lib
#--------------------------------
vlib work

#=======================================
# C O M P I L E
#---------------
vlog -sv pci_master.v pci_target.v pci_protocol_property.sv test_pci_protocol.sv +acc +cover +define+check3

#=======================================
# S I M
#------
vsim -assertdebug -coverage -c test_pci_protocol -l test_pci_protocol_check3.log -do "run -all;quit"