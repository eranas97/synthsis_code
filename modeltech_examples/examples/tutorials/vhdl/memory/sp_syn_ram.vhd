--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   
-- Various VHDL examples: random access memory (RAM)

------------------------------------------------------------------------------
LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE ieee.numeric_std.ALL;

ENTITY sp_syn_ram IS
    GENERIC (
        data_width : positive := 8;
        addr_width : positive := 3
    );
    PORT (
        inclk    : IN  std_logic;
        outclk   : IN  std_logic;
        we       : IN  std_logic;
        addr     : IN  unsigned(addr_width-1 DOWNTO 0);
        data_in  : IN  std_logic_vector(data_width-1 DOWNTO 0);
        data_out : OUT std_logic_vector(data_width-1 DOWNTO 0)
    );

END sp_syn_ram;


ARCHITECTURE intarch OF sp_syn_ram IS

    TYPE mem_type IS ARRAY (0 TO 2**addr_width-1) OF integer;
    SHARED VARIABLE mem : mem_type;

BEGIN

    ASSERT data_width <= 32
        REPORT "### Illegal data width detected"
        SEVERITY failure;

    control_proc : PROCESS (inclk, outclk)
        VARIABLE inner_addr : integer;
        VARIABLE outer_addr : integer;
    BEGIN
        IF (inclk'event AND inclk = '1') THEN
            IF (we = '1') THEN
                mem(to_integer(addr)) := to_integer(unsigned(data_in));
            END IF;
        END IF;

        IF (outclk'event AND outclk = '1') THEN
            data_out <= std_logic_vector(to_unsigned(mem(to_integer(addr)), data_out'length));
        END IF;
    END PROCESS;

END intarch;


ARCHITECTURE constrainedintarch OF sp_syn_ram IS

    SUBTYPE constrained_int is integer range 0 to 2**data_width-1;
    TYPE mem_type IS ARRAY (0 TO 2**addr_width-1) OF constrained_int;
    SHARED VARIABLE mem : mem_type;

BEGIN

    ASSERT data_width <= 32
        REPORT "### Illegal data width detected"
        SEVERITY failure;

    control_proc : PROCESS (inclk, outclk)
        VARIABLE inner_addr : integer;
        VARIABLE outer_addr : integer;
    BEGIN
        IF (inclk'event AND inclk = '1') THEN
            IF (we = '1') THEN
                mem(to_integer(addr)) := to_integer(unsigned(data_in));
            END IF;
        END IF;

        IF (outclk'event AND outclk = '1') THEN
            data_out <= std_logic_vector(to_unsigned(mem(to_integer(addr)), data_out'length));
        END IF;
    END PROCESS;

END constrainedintarch;


ARCHITECTURE \3D\ OF sp_syn_ram IS

    TYPE mem_type IS ARRAY (0 TO 3, 0 TO 2**(addr_width-2)-1) OF integer;
    SHARED VARIABLE mem : mem_type;

BEGIN

    control_proc : PROCESS (inclk, outclk)
        VARIABLE inner_addr : integer;
        VARIABLE outer_addr : integer;
    BEGIN
        IF (inclk'event AND inclk = '1') THEN
            inner_addr := to_integer(addr(addr_width-3 DOWNTO 0));
            outer_addr := to_integer(addr(addr_width-1 DOWNTO addr_width-2));
            IF (we = '1') THEN
                mem(outer_addr, inner_addr) := to_integer(unsigned(data_in));
            END IF;
        END IF;

        IF (outclk'event AND outclk = '1') THEN
            inner_addr := to_integer(addr(addr_width-3 DOWNTO 0));
            outer_addr := to_integer(addr(addr_width-1 DOWNTO addr_width-2));
            data_out <= std_logic_vector(to_unsigned(mem(outer_addr, inner_addr), data_out'length));
        END IF;
    END PROCESS;

END \3D\;

