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

ENTITY ram_tb IS
END ram_tb;

ARCHITECTURE testbench OF ram_tb IS

    -------------------------------------------
    -- Component declaration single-port RAM
    -------------------------------------------
    COMPONENT sp_syn_ram
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
    END COMPONENT;

    -------------------------------------------
    -- Component declaration for dual-port RAM
    -------------------------------------------
    COMPONENT dp_syn_ram
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
    END COMPONENT;

    -------------------------------------------
    -- Intermediate signals and constants
    -------------------------------------------
    SIGNAL   addr     : unsigned(19 DOWNTO 0);
    SIGNAL   inaddr   : unsigned(3 DOWNTO 0);
    SIGNAL   outaddr  : unsigned(3 DOWNTO 0);
    SIGNAL   data_in  : unsigned(31 DOWNTO 0);
    SIGNAL   data_in1 : std_logic_vector(7 DOWNTO 0);
    SIGNAL   data_in2 : std_logic_vector(16 DOWNTO 0);
    SIGNAL   data_in3 : std_logic_vector(31 DOWNTO 0);
    SIGNAL   data_in4 : std_logic_vector(15 DOWNTO 0);
    SIGNAL   data_sp1 : std_logic_vector(7 DOWNTO 0);
    SIGNAL   data_sp2 : std_logic_vector(16 DOWNTO 0);
    SIGNAL   data_sp3 : std_logic_vector(31 DOWNTO 0);
    SIGNAL   data_sp4 : std_logic_vector(15 DOWNTO 0);
    SIGNAL   data_dp1 : std_logic_vector(7 DOWNTO 0);
    SIGNAL   we       : std_logic;
    SIGNAL   clk      : std_logic;
    CONSTANT clk_pd   : time := 100 ns;


BEGIN

    ---------------------------------------------------
    -- instantiations of single-port RAM architectures.
    -- All architectures behave equivalently, but they
    -- have different implementations.  The signal-based
    -- architecture (rtl) is not a recommended style.
    ---------------------------------------------------
    spram1 : entity work.sp_syn_ram(constrainedintarch)
        GENERIC MAP (
            data_width => 8,
            addr_width => 12)
        PORT MAP (
            inclk    => clk,
            outclk   => clk,
            we       => we,
            addr     => addr(11 downto 0),
            data_in  => data_in1,
            data_out => data_sp1);

    spram2 : entity work.sp_syn_ram(constrainedintarch)
        GENERIC MAP (
            data_width => 17,
            addr_width => 11)
        PORT MAP (
            inclk    => clk,
            outclk   => clk,
            we       => we,
            addr     => addr(10 downto 0),
            data_in  => data_in2,
            data_out => data_sp2);

    spram3 : entity work.sp_syn_ram(intarch)
        GENERIC MAP (
            data_width => 32,
            addr_width => 16)
        PORT MAP (
            inclk    => clk,
            outclk   => clk,
            we       => we,
            addr     => addr(15 downto 0),
            data_in  => data_in3,
            data_out => data_sp3);

    spram4 : entity work.sp_syn_ram(\3D\)
        GENERIC MAP (
            data_width => 16,
            addr_width => 8)
        PORT MAP (
            inclk    => clk,
            outclk   => clk,
            we       => we,
            addr     => addr(7 downto 0),
            data_in  => data_in4,
            data_out => data_sp4);

    -------------------------------------------
    -- instantiation of dual-port RAM
    -------------------------------------------
    dpram1 : dp_syn_ram
        GENERIC MAP (
            data_width => 8,
            addr_width => 4)
        PORT MAP (
            inclk    => clk,
            outclk   => clk,
            we       => we,
            inaddr   => inaddr,
            outaddr  => outaddr,
            data_in  => data_in1,
            data_out => data_dp1);

    -------------------------------------------
    -- clock generator
    -------------------------------------------
    clock_driver : PROCESS
    BEGIN
        clk <= '0';
        WAIT FOR clk_pd / 2;
        LOOP
            clk <= '1', '0' AFTER clk_pd / 2;
            WAIT FOR clk_pd;
        END LOOP;
    END PROCESS;

    -------------------------------------------
    -- data-in process
    -------------------------------------------
    datain_drivers : PROCESS(data_in)
    BEGIN
        data_in1 <= std_logic_vector(data_in(7 downto 0));
        data_in2 <= std_logic_vector(data_in(16 downto 0));
        data_in3 <= std_logic_vector(data_in(31 downto 0));
        data_in4 <= std_logic_vector(data_in(15 downto 0));
    END PROCESS;

    -------------------------------------------
    -- simulation control process
    -------------------------------------------
    ctrl_sim : PROCESS
    BEGIN
        FOR i IN 0 TO 1023 LOOP
            we       <= '1';
            data_in  <= to_unsigned(9000 + i, data_in'length);
            addr     <= to_unsigned(i, addr'length);
            inaddr   <= to_unsigned(i, inaddr'length);
            outaddr  <= to_unsigned(i, outaddr'length);
            WAIT UNTIL clk'EVENT AND clk = '0';
            WAIT UNTIL clk'EVENT AND clk = '0';

            data_in  <= to_unsigned(7 + i, data_in'length);
            addr     <= to_unsigned(1 + i, addr'length);
            inaddr   <= to_unsigned(1 + i, inaddr'length);
            WAIT UNTIL clk'EVENT AND clk = '0';
            WAIT UNTIL clk'EVENT AND clk = '0';

            data_in  <= to_unsigned(3, data_in'length);
            addr     <= to_unsigned(2 + i, addr'length);
            inaddr   <= to_unsigned(2 + i, inaddr'length);
            WAIT UNTIL clk'EVENT AND clk = '0';
            WAIT UNTIL clk'EVENT AND clk = '0';

            data_in  <= to_unsigned(30330, data_in'length);
            addr     <= to_unsigned(3 + i, addr'length);
            inaddr   <= to_unsigned(3 + i, inaddr'length);
            WAIT UNTIL clk'EVENT AND clk = '0';
            WAIT UNTIL clk'EVENT AND clk = '0';

            we       <= '0';
            addr     <= to_unsigned(i, addr'length);
            outaddr  <= to_unsigned(i, outaddr'length);
            WAIT UNTIL clk'EVENT AND clk = '0';
            WAIT UNTIL clk'EVENT AND clk = '0';

            addr     <= to_unsigned(1 + i, addr'length);
            outaddr  <= to_unsigned(1 + i, outaddr'length);
            WAIT UNTIL clk'EVENT AND clk = '0';
            WAIT UNTIL clk'EVENT AND clk = '0';

            addr     <= to_unsigned(2 + i, addr'length);
            outaddr  <= to_unsigned(2 + i, outaddr'length);
            WAIT UNTIL clk'EVENT AND clk = '0';
            WAIT UNTIL clk'EVENT AND clk = '0';

            addr     <= to_unsigned(3 + i, addr'length);
            outaddr  <= to_unsigned(3 + i, outaddr'length);
            WAIT UNTIL clk'EVENT AND clk = '0';
            WAIT UNTIL clk'EVENT AND clk = '0';

        END LOOP;
        ASSERT false
            REPORT "### End of Simulation!"
            SEVERITY failure;
    END PROCESS;

END testbench;
