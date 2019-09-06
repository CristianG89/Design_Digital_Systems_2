library IEEE;
use IEEE.STD_LOGIC_1164.ALL;
use IEEE.NUMERIC_STD.ALL;

entity alu is
	port (
		Clk :	in std_logic;			--clock signal
		A,B :	in signed(31 downto 0);		--input operands
		Op :	in unsigned(2 downto 0);	--Operation to be performed
		R :	out signed(31 downto 0)		--output of ALU
	);
end alu;

architecture Behavioral of alu is
	--temporary signal declaration.
	signal Reg1,Reg2,Reg3 : signed(31 downto 0) := (others => '0');

	begin

	Reg1 <= A;
	Reg2 <= B;
	R <= Reg3;

	process(Clk)
	variable temp : signed(63 downto 0) := (others => '0');		--Variable needed to hold multiplication temporary value
	
	begin
		if(rising_edge(Clk)) then --Do the calculation at the positive edge of clock cycle.
			case Op is
				when "000" =>
					Reg3 <= Reg1 + Reg2;  	--addition
				when "001" =>
					Reg3 <= Reg1 - Reg2; 	--subtraction
				when "010" =>
					temp := Reg1 * Reg2; 	--multiplication	--XOR removed (not required here) and multiplication added (and reordered) instead.
					Reg3 <= temp(31 downto 0);			--As multiplication gives a 64 bits value, an intermediate variable (not register!) is needed.
				when "011" =>
					Reg3 <= not Reg1;  		--NOT gate
				when "100" =>
					Reg3 <= Reg1 nand Reg2; --NAND gate
				when "101" =>
					Reg3 <= Reg1 nor Reg2; 	--NOR gate
				when "110" =>
					Reg3 <= Reg1 and Reg2;  --AND gate
				when "111" =>
					Reg3 <= Reg1 or Reg2;  	--OR gate
				when others =>
					NULL;
			end case;
		end if;
	end process;

end Behavioral;
