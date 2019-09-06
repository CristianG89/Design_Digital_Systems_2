library IEEE;
use IEEE.std_logic_1164.all;

entity dff is
 port(
  clk : in  std_ulogic;
  d_i : in  std_ulogic;
  q_o : out std_ulogic
 );
end dff;

architecture rtl of dff is
begin
 process is
 begin
  wait until clk'event and clk = '1';
  q_o <= d_i;
 end process;
end rtl;
