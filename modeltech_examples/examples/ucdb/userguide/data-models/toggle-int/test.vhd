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
    signal x : integer := 0;
    begin
    branch: process
        variable myoutput : line;
    begin
        wait until x'event;
        write(myoutput,x);
        writeline(output,myoutput);
    end process branch;
    drive: process
    begin
        wait for 10 ns;
        x <= 1;
        wait;
    end process drive;
end architecture;
