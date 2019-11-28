-- UCDB API User Guide Example
--
-- Copyright 2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
-- PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
-- LICENSE TERMS.

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use std.textio.all;
entity top is
end;
architecture arch of top is
    signal x : std_logic := '0';
    signal y: std_logic := '0';
    begin
    branch: process
        variable myoutput : line;
    begin
        wait until x'event or y'event;
        if (x = '1') then
            write(myoutput,string'("x is true"));
            writeline(output,myoutput);
        elsif (y = '1') then
            write(myoutput,string'("y is true"));
            writeline(output,myoutput);
        end if;
    end process branch;
    drive: process
    begin
        wait for 10 ns;
        x <= '1';
        wait for 10 ns;
        x <= '0';
        wait for 10 ns;
        y <= '1';
        wait;
    end process drive;
end architecture;
