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

architecture proc_seq of proc is

constant c_IF : unsigned := "001";
constant c_ID : unsigned := "010";
constant c_EX : unsigned := "011";
constant c_MEM : unsigned := "100";
constant c_WB : unsigned := "101";

signal REG_FILE : TypeArrayDataWord(7 downto 0);  -- note: index 0 is not used!

signal CONTROL_STATE : unsigned (2 downto 0);

signal DADDR : TypeDataAddr;

signal PC : TypeInstrAddr;
signal A, B, DOUT, DIN, TEMP : TypeDataWord;
signal IR : TypeInstr;

signal DATA_WRITE : bit;

begin

instrAddr <= PC;
dataOut <= DOUT;
dataAddr <= DADDR;
writeEnable <= DATA_WRITE;

process
variable immediate_branch : TypeInstrAddr;
variable immediate_jump : TypeInstrAddr;
variable immediate_alu : TypeDataWord;
variable operandB : TypeDataWord;
begin
	wait until clk'event and clk='1';

	DATA_WRITE <= '0';

	if( reset = '1' ) then
		CONTROL_STATE <= c_IF;
		PC <= (others => '0');
		IR <= (others => '0');

	elsif CONTROL_STATE = c_IF then		-- FETCH
			PC <= PC + 2;

			IR <= instrIn;
			CONTROL_STATE <= c_ID;

	elsif CONTROL_STATE = c_ID then		-- DECODE

		if( op1(IR) /= c_REG_NULL ) then
			A <= REG_FILE( CONV_INTEGER(op1(IR)) );
		else
			A <= c_NULL_WORD;
		end if;

		if( op2(IR) /= c_REG_NULL ) then
			B <= REG_FILE( CONV_INTEGER(op2(IR)) );
		else
			B <= c_NULL_WORD;
		end if;

		if( IR(8) = '0' ) then		-- sign extension
			immediate_branch := c_NULL_BRANCH & IR(8 downto 0);
		else
			immediate_branch := c_ONE_BRANCH & IR(8 downto 0);
		end if;

		if( IR(11) = '0' ) then		-- sign extension
			immediate_jump := c_NULL_JUMP & IR(11 downto 0);
		else
			immediate_jump := c_ONE_JUMP & IR(11 downto 0);
		end if;

		if( opcode(IR) = c_BRANCH ) then
			if( op1(IR) = c_REG_NULL ) then
				PC <= PC + immediate_branch;
			elsif( REG_FILE( CONV_INTEGER(op1(IR)) ) = c_NULL_WORD ) then
				PC <= PC + immediate_branch;
			end if;
			CONTROL_STATE <= c_IF;
		elsif( opcode(IR) = c_JUMP ) then 
			PC <= PC + immediate_jump;
			CONTROL_STATE <= c_IF;
		else
			CONTROL_STATE <= c_EX;
		end if;

	elsif CONTROL_STATE = c_EX then		-- EX
		if( IR(5) = '0' ) then			-- sign extension
			immediate_alu := c_NULL_ALU & IR(5 downto 0);
		else
			immediate_alu := c_ONE_ALU & IR(5 downto 0);
		end if;

		if( opcode(IR) = c_STORE ) then
			DOUT <= B;
			DATA_WRITE <= '1';
		elsif( opcode(IR) = c_ALU_REG ) then
			operandB := B;
		elsif( opcode(IR) = c_ADD_IMM or opcode(IR) = c_OR_IMM ) then
			operandB := immediate_alu;
		end if;

		if( (opcode(IR) = c_ALU_REG and IR(2 downto 0) = c_ADD) or
			opcode(IR) = c_ADD_IMM ) then
				TEMP <= A + operandB;
		end if;

		if( (opcode(IR) = c_ALU_REG and IR(2 downto 0) = c_OR) or
			opcode(IR) = c_OR_IMM ) then
				for i in TEMP'range loop
					TEMP(i) <= A(i) or operandB(i);
				end loop;
		end if;

		if( opcode(IR) = c_LOAD or opcode(IR) = c_STORE ) then
			DADDR <= A + immediate_alu;
		end if;

		CONTROL_STATE <= c_MEM;

	elsif CONTROL_STATE = c_MEM then	-- MEM
		if( opcode(IR) = c_LOAD ) then
			DIN <= dataIn;
		end if;

		CONTROL_STATE <= c_WB;

	elsif CONTROL_STATE = c_WB then		-- WB
		if( opcode(IR) = c_LOAD and op2(IR) /= c_REG_NULL ) then
			REG_FILE( CONV_INTEGER(op2(IR)) ) <= DIN;
		elsif( opcode(IR) = c_ALU_REG and op3(IR) /= c_REG_NULL ) then
			REG_FILE( CONV_INTEGER(op3(IR)) ) <= TEMP;
		elsif( (opcode(IR) = c_ADD_IMM or opcode(IR) = c_OR_IMM) and
				op2(IR) /= c_REG_NULL ) then
			REG_FILE( CONV_INTEGER(op2(IR)) ) <= TEMP;
		end if;

		CONTROL_STATE <= c_IF;
	end if;
end process;
end;