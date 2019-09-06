--
--   Author: Joachim Horch
--     Date: October 2000
--
------------------------------------------------------------------------------------------
------------------------------------------------------------------------------------------

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.std_logic_arith.all;

package proc_package is

subtype TypeInstr is unsigned( 15 downto 0 );

subtype TypeInstrAddr is unsigned( 15 downto 0 );

subtype TypeDataAddr is unsigned( 7 downto 0 );
subtype TypeDataWord is unsigned( 7 downto 0 );

subtype TypeRegAddr is unsigned( 2 downto 0 );
subtype TypeExInstr is unsigned( 8 downto 0 );	-- opcode and op1 not used anymore

subtype TypeOpcode is unsigned( 3 downto 0 );

subtype TypeAluOp is unsigned( 2 downto 0 );

type    TypeArrayDataWord is array (natural range <>) of TypeDataWord;

constant c_ALU_REG : TypeOpcode := "0001";

constant c_ADD_IMM : TypeOpcode := "0010";
constant c_OR_IMM  : TypeOpcode := "0011";

constant c_LOAD    : TypeOpcode := "0100";
constant c_STORE   : TypeOpcode := "0101";

constant c_JUMP    : TypeOpcode := "0110";
constant c_BRANCH  : TypeOpcode := "0111";

constant c_ADD     : TypeAluOp := "001";
constant c_OR      : TypeAluOp := "010";

constant c_REG_NULL : unsigned( 2 downto 0 ) := (others => '0');
constant c_NULL_WORD : unsigned( 7 downto 0 ) := (others => '0');

constant c_NULL_ALU : unsigned( 1 downto 0 ) := (others => '0');
constant c_ONE_ALU : unsigned( 1 downto 0 ) := (others => '1');

constant c_NULL_BRANCH : unsigned( 6 downto 0 ) := (others => '0');
constant c_ONE_BRANCH : unsigned( 6 downto 0 ) := (others => '1');

constant c_NULL_JUMP : unsigned( 3 downto 0 ) := (others => '0');
constant c_ONE_JUMP : unsigned( 3 downto 0 ) := (others => '1');

function opcode( ir : unsigned ) return unsigned;
function op1( ir : unsigned ) return unsigned;
function op2( ir : unsigned ) return unsigned;
function op3( ir : unsigned ) return unsigned;

end;

package body proc_package is

function opcode( ir : unsigned ) return unsigned is
begin
	return ir(15 downto 12);
end;

function op1( ir : unsigned ) return unsigned is
begin
	return ir(11 downto 9);
end;

function op2( ir : unsigned ) return unsigned is
begin
	return ir(8 downto 6);
end;

function op3( ir : unsigned ) return unsigned is
begin
	return ir(5 downto 3);
end;

end;
