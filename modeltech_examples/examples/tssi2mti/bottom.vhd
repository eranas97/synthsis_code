library ieee;
use ieee.std_logic_1164.all;

entity bottom is
    port(
        i               : in    std_logic;
        io              : inout std_logic;
        o               : out   std_logic
    );
end bottom;

architecture arch of bottom is
begin
process
begin
    io <= '0';
    o  <= '0';
	wait for 10 ns;

    io <= '1';
    o  <= '1';
	wait for 10 ns;
end process;
end;
