--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
-- WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
-- OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--

-- Filename    : test_ringbuf.vhd
--
-- Description : Test Bench

library ieee, work;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.std_logic_unsigned.all;
use std.textio.all ;

ENTITY test_ringbuf IS
END test_ringbuf;

ARCHITECTURE test_ringbuf_arch OF test_ringbuf IS
    COMPONENT ringbuf
        PORT (
            clock : IN std_logic;
            reset : IN std_logic;
            txda : IN std_logic;
            rxda : OUT std_logic;
            txc : OUT std_logic;
            outstrobe : OUT std_logic
        );
    END component;

    SIGNAL clock : std_logic := '0';
    SIGNAL reset, txda, rxda, txc    : std_logic;
    SIGNAL addrs : std_logic_vector(15 DOWNTO 0);
    SIGNAL pseudo : std_logic_vector(19 DOWNTO 0);
    SIGNAL storage : std_logic_vector(19 DOWNTO 0);
    SIGNAL expected, outstrobe, actual, dataerror : std_logic;

BEGIN

    Gen_Reset : PROCESS
    BEGIN
       reset <= '0';
       WAIT FOR 400 NS;
       reset <= '1';
       WAIT FOR 1000000 NS;
       WAIT;
    END PROCESS;

    Gen_Clock : clock <= not(clock) after 100 ns;

    Generate_Data : PROCESS (txc, reset)
    BEGIN
        IF (reset = '0') THEN
            pseudo <= "00000000000000000000";
        ELSIF (txc'event AND txc = '1') THEN
            pseudo <= pseudo(18 DOWNTO 0) & NOT (pseudo(2) XOR pseudo(19));
        END IF;
    END PROCESS;

    --
    -- Assigns the output from the LFSR to the transmit data input
    -- into the device
    --
    txda <= pseudo(19);

    --
    -- This section puts the data that comes out of the ring buf into
    -- a LFSR with the same taps as the generated data. It then compares
    -- this data with the next bit to ensure that the data is correct.
    --
    Compare_Data : PROCESS (clock)
    BEGIN
        IF (clock'event AND clock = '0') THEN
            IF reset = '0' THEN
                storage <= "00000000000000000000";
                expected <= '0';
            ELSIF outstrobe = '1' THEN
                storage <= storage(18 DOWNTO 0) & rxda;
                expected <= NOT (storage(2) XOR storage(19));
            END IF;
        END IF;
    END PROCESS;

    actual <= storage(0);

    Produce_Error_Sig : PROCESS (clock)
    BEGIN
        IF (clock'event AND clock = '0') THEN
            IF (reset = '0') THEN
                dataerror <= '0';
            ELSE
                dataerror <= NOT (actual XOR expected);
            END IF;
        END IF;
    END PROCESS;

    print_error : PROCESS (dataerror)
        variable line_out: Line;
    BEGIN
        IF (dataerror'event AND dataerror = '0' AND now > 600 ns) THEN
            write(line_out,string'("** NOTICE ** at ") );
            write(line_out, now );
            write(line_out,string'(" : Data value not expected.") );
            writeline(OUTPUT, line_out);
       END IF;
    END PROCESS;

    print_restore : PROCESS (dataerror)
        variable line_out: Line;
    BEGIN
        IF (dataerror'event AND dataerror = '1' AND now > 600 ns) THEN
            write(line_out,string'("** RESTORED ** at ") );
            write(line_out, now );
            write(line_out,string'(" : Data returned to expected value.") );
            writeline(OUTPUT, line_out);
        END IF;
    END PROCESS;

    chip: ringbuf
    PORT MAP (
        clock => clock,
        reset => reset,
        txda => txda,
        rxda => rxda,
        txc => txc,
        outstrobe => outstrobe
    );

END test_ringbuf_arch;
