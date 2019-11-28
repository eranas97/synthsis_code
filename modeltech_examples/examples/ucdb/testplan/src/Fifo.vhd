-- Fifo function

library IEEE;
use IEEE.STD_LOGIC_1164.all;

entity FIFOCELL is
  port (CLOCK: in STD_LOGIC;
        RESET: in STD_LOGIC;
        STATUS_IN: in STD_LOGIC;
        SHIFT_IN: out STD_LOGIC;
        SHIFT_OUT: in STD_LOGIC;
        STATUS_OUT: out STD_LOGIC;
        DIN: in STD_LOGIC;
        DOUT: out STD_LOGIC);
end;

architecture RTL of FIFOCELL is
signal CONDITION: STD_LOGIC;
signal STORE: STD_LOGIC;
begin
FIFOCELL: process
begin
  wait until RISING_EDGE (CLOCK);
  if (CONDITION = '1' and SHIFT_OUT = '1') or RESET = '0' then
    CONDITION <= '0';
  elsif STATUS_IN = '1' and CONDITION = '0' then
    CONDITION <= '1';
  else
    CONDITION <= CONDITION;
  end if;
  if RESET = '0' then
    DOUT <= '0';
  elsif STORE = '1' then
    DOUT <= DIN;
  end if;
  if RESET = '0' then
    STORE <= '0';
  elsif (CONDITION = '0' and STATUS_IN = '1') or
        (CONDITION = '1' and SHIFT_OUT = '1') then
    STORE <= '1';
  else
    STORE <= '0';
  end if;
end process;

STATUS_OUT <= CONDITION;
SHIFT_IN <= STORE;

end RTL;

-- End Of VHDL FILE
