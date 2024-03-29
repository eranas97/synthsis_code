--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
-- WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
-- OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--

-- Filename    : store.vhd
--
-- Description : Register storage for incoming data.

library ieee, std, std_developerskit;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.std_logic_unsigned.all;
USE std.textio.all;
USE std_developerskit.std_iopak.all;

ENTITY store IS
    GENERIC (
        counter_size : integer := 4;
        buffer_size : integer := 16
    );
    PORT (
        clock    : IN std_logic;
        reset    : IN std_logic;
        oeenable : IN std_logic;
        txda     : INOUT std_logic;
        ramadrs  : IN std_logic_vector((counter_size *2) DOWNTO 0);
        buffers  : OUT std_logic_vector((buffer_size-1) DOWNTO 0)
    );
END store;

ARCHITECTURE RTL OF store IS
    signal sig1: std_logic;
    signal sig2: boolean;
    signal sig3: std_logic_vector(3 downto 0);
    signal sig4: std_logic_vector(0 to 2);
BEGIN

    print_signals: process(sig3)
        variable line_out: Line;
    BEGIN
        write(line_out, string'("sig1="), left);
        write(line_out, TO_String(sig1, "%1s"));
        writeline(OUTPUT, line_out);

        write(line_out, string'("sig2="), left);
        write(line_out, sig2);
        writeline(OUTPUT, line_out);

        write(line_out, string'("sig3="), left);
        write(line_out, TO_String(sig3, "%4s"));
        writeline(OUTPUT, line_out);

        write(line_out, string'("sig4="), left);
        write(line_out, TO_String(sig4, "%3s"));
        writeline(OUTPUT, line_out);
    END PROCESS;

    txda <= 'Z';

    --
    -- This process produces a n-bit register along
    -- with decode logic to load each of the bits
    -- in the register.
    --
    Storer : PROCESS (clock)
    variable address : integer range 0 to (buffer_size - 1);
    variable line_out: Line;
    BEGIN
        IF (clock'event AND clock = '1') THEN
            IF (reset = '0') THEN
                buffers <= (others => '0');
            ELSIF (oeenable = '0') THEN
                address := conv_integer(ramadrs((counter_size * 2) downto (counter_size + 1)));
                buffers(address) <= txda;
            END IF;
        END IF;
    END PROCESS;

END RTL;
