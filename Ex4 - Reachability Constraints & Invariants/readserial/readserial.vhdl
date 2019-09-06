-- serial receiver
--
-- Design description:
--
-- This module watches an input line, 'rxd', for serial transmissions of bytes
-- (8 bits). A transmission begins with a '0' start bit, followed by 8 data
-- bits.
-- Byte transmissions may follow each other immediately.
-- If after a transmission the input line is '1' the transmission is considered
-- 'idle' and the receiver waits for a start bit.
--
-- There is no parity bit and no stop bit.
--
-- Dominik Stoffel, 2009-01-23

library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;

entity readserial is
	port (
		clk     : in  std_ulogic;                     -- clock signal
		reset_n : in  std_ulogic;                     -- reset signal
		rxd     : in  std_ulogic;                     -- serial in
		data    : out std_ulogic_vector(7 downto 0);  -- data out
		valid   : out std_ulogic	                  -- data valid
	);
end entity readserial;

architecture rtl of readserial is
  type state_t is (IDLE, READDATA);
  signal state_s : state_t;

  signal data_i : std_ulogic_vector(7 downto 0);  -- internal data register
  signal cnt_s : integer range 0 to 7;  -- counter
  signal cnt_en : std_ulogic;           -- counter enable
  
begin  -- architecture rtl

  counter: process (clk, reset_n) is
  begin  -- process counter
    if reset_n = '0' then               -- asynchronous reset (active low)
      cnt_s <= 0; 
    elsif clk'event and clk = '1' then  -- rising clock edge
      if cnt_en = '1' then
        cnt_s <= (cnt_s + 1) mod 8; 
      end if;
    end if;
  end process counter;

  shiftreg: process (clk) is
  begin  -- process register
    if clk'event and clk = '1' then  -- rising clock edge
      data_i(7 downto 1) <= data_i(6 downto 0);
      data_i(0) <= rxd; 
    end if;
  end process shiftreg;

  ctrl: process (clk, reset_n) is
  begin  -- process ctrl
    if reset_n = '0' then               -- asynchronous reset (active low)
      state_s <= IDLE;
      valid <= '0';
      cnt_en <= '0'; 
    elsif clk'event and clk = '1' then  -- rising clock edge
      case state_s is
        when IDLE =>
          if rxd = '0' then
            state_s <= READDATA;
            cnt_en <= '1'; 
          end if;
          valid <= '0'; 
        when READDATA =>
          if cnt_s = 7 then
            state_s <= IDLE;
            valid <= '1';
            cnt_en <= '0'; 
          end if;
      end case;
    end if;
  end process ctrl;
  
  -- The data output always presents the state of the internal shift register.
  data <= data_i;

end architecture rtl;