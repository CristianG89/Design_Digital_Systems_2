library IEEE;
use IEEE.std_logic_1164.all;

entity jkff is
  port (
    clk : in std_ulogic;
    j_i : in std_ulogic;
    k_i : in std_ulogic;
    q_o : out std_ulogic);
end entity jkff;


architecture rtl of jkff is

  component dff
    port (
      clk : in  std_ulogic;
      d_i : in  std_ulogic;
      q_o : out std_ulogic);
  end component;

  signal d : std_ulogic;
  signal q : std_ulogic; 

  
begin  -- rtl
  d <= (not q and j_i) or (q and not k_i);
  
  inst_dff: dff
     port map (
       clk => clk,
       d_i => d, 
       q_o => q);

  q_o <= q; 
end architecture rtl;

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

