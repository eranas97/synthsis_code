library IEEE;
use IEEE.STD_LOGIC_1164.all;

entity FS_ADD_MUX is
  port (A: in STD_LOGIC_VECTOR(18 downto 0);
        B: in STD_LOGIC_VECTOR(18 downto 0);
        SEL: in STD_LOGIC;
        SWITCH: out STD_LOGIC_VECTOR(18 downto 0));
end;

architecture RTL of FS_ADD_MUX is
begin
  MUX: process (A,B,SEL)
  begin
    if SEL = '1' then
      SWITCH <= A;
    else
      SWITCH <= B;
    end if;
  end process;
end RTL;
