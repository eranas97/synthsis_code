library ieee;
use ieee.std_logic_1164.all;

entity middle is
    port(
        i               : in    std_logic;
        io              : inout std_logic;
        o               : out   std_logic
    );
end middle;

architecture arch of middle is

    component bottom
        port(
            i   : in    std_logic;
            io  : inout std_logic;
            o   : out   std_logic 
        );
    end component;

begin
    b: bottom  port map(i, io, o);
end;
