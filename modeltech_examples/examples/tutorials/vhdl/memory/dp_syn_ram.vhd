--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   
-- Simple VHDL example: random access memory (RAM)

------------------------------------------------------------------------------
LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;

ENTITY dp_syn_ram IS
    GENERIC (
        data_width : positive := 8;
        addr_width : positive := 3
    );
    PORT (
        inclk    : IN  std_logic;
        outclk   : IN  std_logic;
        we       : IN  std_logic;
        inaddr   : IN  unsigned(addr_width-1 DOWNTO 0);
        outaddr  : IN  unsigned(addr_width-1 DOWNTO 0);
        data_in  : IN  std_logic_vector(data_width-1 DOWNTO 0);
        data_out : OUT std_logic_vector(data_width-1 DOWNTO 0)
    );
END dp_syn_ram;

ARCHITECTURE rtl OF dp_syn_ram IS

    TYPE mem_type IS ARRAY (0 TO (2**addr_width)-1) OF std_logic_vector(data_width-1 DOWNTO 0);
    SIGNAL mem : mem_type;

BEGIN

    write_proc : PROCESS (we, inclk, inaddr)
    BEGIN
        IF (inclk'event AND inclk = '1') THEN
            IF (we = '1') THEN
                mem(to_integer(inaddr)) <= data_in;
            END IF;
        END IF;
    END PROCESS;

    read_proc : PROCESS (outclk, outaddr)
    BEGIN
        IF (outclk'event AND outclk = '1') THEN
            data_out <= mem(to_integer(outaddr));
        END IF;
    END PROCESS;

END rtl;

