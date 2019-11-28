--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

-- Filename    : control.vhd
-- 
-- Description : This block produces the address generation
--               and strobe generation for input and output
--               data.

library ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.std_logic_unsigned.all;

ENTITY control IS
    GENERIC (
        counter_size : integer := 4
    );
    PORT (
        clock     : IN std_logic;
        reset     : IN std_logic;
        ramadrs   : OUT std_logic_vector((counter_size * 2) DOWNTO 0);
        oeenable  : OUT std_logic;
        outstrobe : OUT std_logic;
        txc       : OUT std_logic
    );
END control;

ARCHITECTURE RTL OF control IS
    signal address: std_logic_vector((counter_size * 2) DOWNTO 0);
BEGIN

    -- This process creates an N-bit counter
    Incrementer : PROCESS (clock)
    BEGIN
        IF (clock'event AND clock = '1') THEN
            IF reset = '0' THEN
                address <= (others => '0');
            ELSE
                address <= address + '1';
            END IF;
        END IF;
    END PROCESS;

    -- This process generates the oeenable strobe used by the data store
    Enable_gen : PROCESS (clock)
    BEGIN
        IF (clock'event AND clock = '1') THEN
            IF reset = '0' THEN
                oeenable <= '0';
            ELSIF (address(counter_size DOWNTO 0) = 0) THEN
                oeenable <= '1';
            ELSE
                oeenable <= '0';
            END IF;
        END IF;
    END PROCESS;

    --
    -- This process implements the outstrobe
    -- signal that is used to show when data output by the 
    -- device is valid 
    --
    OutStrobe_gen : PROCESS (address)
        variable x : std_logic;
    BEGIN
        x := '1';
        for i in counter_size to (counter_size * 2) loop
          x := x and address(i);
        end loop ;
        outstrobe <= x;
    END PROCESS;

    ramadrs <= address;
    txc <= address(counter_size);

END RTL;
