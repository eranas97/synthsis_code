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

    txda <= 'Z';

    assign_observed_value: PROCESS (clock)
    variable line_out: Line;
    variable state: integer := 0;
    BEGIN
        IF (clock'event AND clock = '1') THEN
            IF (state = 0) THEN
                write(line_out, string'("VHDL drives sig1=1, sig2=TRUE, sig3=0101, sig4=100"), left);
                writeline(OUTPUT, line_out);
                sig1 <= '1';
                sig2 <= TRUE;
                sig3 <= "0101";
                sig4 <= "100";
                state := 1;
            ELSIF (state = 1) THEN
                write(line_out, string'("VHDL drives sig1=0, sig2=FALSE, sig3=0000, sig4=111"), left);
                writeline(OUTPUT, line_out);
                sig1 <= '0';
                sig2 <= FALSE;
                sig3 <= "0000";
                sig4 <= "111";
                state := 2;
            ELSIF (state = 2) THEN
                write(line_out, string'("VHDL drives sig1=0, sig2=TRUE, sig3=1111, sig4=001"), left);
                writeline(OUTPUT, line_out);
                sig1 <= '0';
                sig2 <= TRUE;
                sig3 <= "1111";
                sig4 <= "001";
                state := 3;
            ELSE
                write(line_out, string'("VHDL drives sig1=1, sig2=FALSE, sig3=0111, sig4=011"), left);
                writeline(OUTPUT, line_out);
                sig1 <= '1';
                sig2 <= FALSE;
                sig3 <= "0111";
                sig4 <= "011";
                state := 0;
            END IF;
        END IF;
    END PROCESS;

    --
    -- This process produces a n-bit register along
    -- with decode logic to load each of the bits
    -- in the register.
    --
    Storer : PROCESS (clock)
    variable address : integer range 0 to (buffer_size - 1);
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
