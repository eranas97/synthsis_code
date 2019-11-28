--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
-- WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
-- OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--

-- Filename    : ringbuf.vhd
--
-- Description : Top Level

library ieee;
USE ieee.std_logic_1164.all;
USE std.textio.all;

ENTITY ringbuf IS
    generic (
        int_param : integer;
        real_param : real;
        str_param : string;
        bool_param : boolean;
        char_param : character;
        bit_param : bit;
        bv_param : bit_vector(0 to 2);
        logic_param : std_logic;
        lv_param : std_logic_vector(3 downto 0));
    PORT (
        clock     : IN std_logic;
        reset     : IN std_logic;
        txda      : INOUT std_logic;
        rxda      : INOUT std_logic;
        txc       : OUT std_logic;
        outstrobe : OUT std_logic;
        buffers   : INOUT std_logic_vector(15 DOWNTO 0)
    );

END ringbuf;


ARCHITECTURE RTL OF ringbuf IS
    signal sig1: std_logic;
    signal sig2: std_logic_vector(3 downto 0);

BEGIN
    sig1 <= logic_param;
    sig2 <= lv_param;

    print_param: PROCESS
        variable line_out: Line;
    BEGIN
        write(line_out, string'("int_param="), left);
        write(line_out, int_param);
        writeline(OUTPUT, line_out);
        write(line_out, string'("real_param="), left);
        write(line_out, real_param);
        writeline(OUTPUT, line_out);
        write(line_out, string'("str_param="), left);
        write(line_out, str_param);
        writeline(OUTPUT, line_out);
        write(line_out, string'("bool_param="), left);
        write(line_out, bool_param);
        writeline(OUTPUT, line_out);
        write(line_out, string'("char_param="), left);
        write(line_out, char_param);
        writeline(OUTPUT, line_out);
        write(line_out, string'("bit_param="), left);
        write(line_out, bit_param);
        writeline(OUTPUT, line_out);
        write(line_out, string'("bv_param="), left);
        write(line_out, bv_param);
        writeline(OUTPUT, line_out);
        WAIT FOR 20 NS;
    END PROCESS;
END RTL;
