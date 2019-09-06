
library IEEE;
use IEEE.std_logic_1164.all;

entity arbiter is
  
  port (
    clk       : in  std_logic;
    reset     : in  std_logic;
    request_i : in  std_logic_vector(1 downto 0);
    grant_o   : out std_logic_vector(1 downto 0);
    free_i    : in  std_logic);

end entity arbiter;


architecture rtl of arbiter is
  type state_type is (IDLE, BUSY);
  signal state_s : state_type;
  signal last_grant_s : natural range 0 to 1;        -- index of master last granted access to the resource

begin  -- architecture rtl

  process (clk, reset) is
    variable master_v : natural range 0 to 1;      -- auxiliary variable for priority calculation
  begin  -- process
    if reset = '1' then                 -- asynchronous reset (active high)
      last_grant_s <= 1; 
      state_s <= IDLE; 
      grant_o <= "00"; 
    elsif clk'event and clk = '1' then  -- rising clock edge
      case state_s is
        when IDLE =>
          if free_i = '1' and (request_i(0) = '1' or request_i(1) = '1') then
            state_s <= BUSY;
            case request_i is
              when "01" => master_v := 0 ;
              when "10" => master_v := 1 ;
              when "11" => if (last_grant_s = 0) then master_v := 1; else master_v := 0; end if; 
              when others => null;
            end case;
            grant_o(master_v) <= '1';
            last_grant_s <= master_v;
          end if;

        when BUSY =>
          grant_o <= "00"; 
          state_s <= IDLE; 
      end case;
    end if;
  end process;

end architecture rtl;
