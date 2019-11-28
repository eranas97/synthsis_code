library ieee;
use ieee.std_logic_1164.all;

entity top is end;

architecture arch of top is

    component middle
        port(
            i   : in    std_logic;
            io  : inout std_logic;
            o   : out   std_logic 
        );
    end component;

    signal i    : std_logic;
    signal io   : std_logic;
    signal o    : std_logic;

begin
    m: middle  port map(i, io, o);
process
begin
	i  <= '0';
	io <= '0';
	wait for 10 ns;

	i  <= '1';
	io <= '1';
	wait for 10 ns;
end process;
end;
