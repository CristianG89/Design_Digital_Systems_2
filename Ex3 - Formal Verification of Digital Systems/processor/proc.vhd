--
--   Author: Joachim Horch
--     Date: October 2000
--
------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------

library ieee;
use ieee.std_logic_arith.all;
use ieee.std_logic_1164.all;

library work;
use work.proc_package.all;

entity proc is
port		(
				instrIn : in TypeInstr;
				instrAddr : out TypeInstrAddr;
				dataIn : in TypeDataWord;
				dataOut : out TypeDataWord;
				dataAddr : out TypeDataAddr;
				writeEnable : out bit;
				clk : in bit;
				reset : in bit := '0'
			);
end proc;
