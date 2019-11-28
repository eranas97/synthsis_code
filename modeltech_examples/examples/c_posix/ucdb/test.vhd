library IEEE;
use IEEE.STD_LOGIC_1164.all;

entity VHDL_COLOR is
  port (CLK: in STD_LOGIC;
        PRIMARY_YELLOW: in STD_LOGIC;
        PRIMARY_RED: in STD_LOGIC;
        PRIMARY_BLUE: in STD_LOGIC);
end;

architecture ARCH_COLOR of VHDL_COLOR is
signal SECONDARY_ORANGE: STD_LOGIC;
signal SECONDARY_PURPLE: STD_LOGIC;
signal SECONDARY_GREEN: STD_LOGIC;
signal ORANGE: STD_LOGIC;
signal PURPLE: STD_LOGIC;
signal GREEN: STD_LOGIC;
signal IS_PRIMARY: STD_LOGIC;
signal IS_BLACK: STD_LOGIC;

begin
COLOR_ARCH: process
begin
  wait until RISING_EDGE (CLK);
  SECONDARY_ORANGE <= '0';
  SECONDARY_GREEN <= '0';
  ORANGE <= '0';
  PURPLE <= '0';
  GREEN <= '0';
  IS_PRIMARY <= '0';
  if (PRIMARY_YELLOW = '1') and (PRIMARY_RED = '1') then 
      SECONDARY_ORANGE <= '1'; 
  end if;
  if NOT ((PRIMARY_YELLOW = '1') and (PRIMARY_BLUE = '1')) then else 
      SECONDARY_GREEN <= '1';
  end if;
  if (PRIMARY_RED = '1') and (PRIMARY_BLUE = '1') then 
      SECONDARY_PURPLE <= '1';  
  else 
      SECONDARY_PURPLE <= '0';
  end if;
  if (PRIMARY_RED = '1') and (PRIMARY_YELLOW = '1') then 
      ORANGE <= '1';
  elsif (PRIMARY_BLUE = '1') and (PRIMARY_RED = '1') then
      PURPLE <= '1';
  elsif (PRIMARY_BLUE = '1') and (PRIMARY_YELLOW = '1') then
      GREEN <= '1';
  else 
      IS_PRIMARY <= '1';
  end if;
  case ((PRIMARY_YELLOW = '1') and (PRIMARY_RED = '1') and (PRIMARY_BLUE = '1')) is
      when true => IS_BLACK <= '1';
      when others => IS_BLACK <= '0';
  end case;
end process COLOR_ARCH;

end ARCH_COLOR;

library IEEE;
use IEEE.STD_LOGIC_1164.all;

entity VHDL_TOGGLE is
  port (CLK: in STD_LOGIC);
end;

architecture ARCH_TOGGLE of VHDL_TOGGLE is
type enumT is (one, two, three, four);
signal state : integer := 1;
signal enumS : enumT := one;
signal ssls : std_ulogic := '0';
signal sbts : bit := '0';
signal sslv : std_ulogic_vector (1 downto 0) := "01";
signal sbtv : bit_vector (1 downto 0) := "01";

begin
TOGGLE_ARCH: process
begin
  wait until RISING_EDGE (CLK);
  case (state) is
      when 1 =>
          state <= 2;
          enumS <= two;
          ssls <= '1';
          sbts <= '1';
          sslv <= "10";
          sbtv <= "10";
      when 2 =>
          state <= 3;
          enumS <= three;
          ssls <= 'Z';
          sslv <= "ZZ";
          sbtv <= "11";
      when others =>
          state <= 1;
          enumS <= one;
          ssls <= '0';
          sbts <= '0';
          sslv <= "01";
          sbtv <= "01";
  end case;

end process TOGGLE_ARCH;
end ARCH_TOGGLE;

