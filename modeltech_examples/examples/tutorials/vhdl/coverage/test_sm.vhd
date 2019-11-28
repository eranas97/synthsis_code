--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

use std.textio.all;

library IEEE;
use IEEE.std_logic_1164.all;
use ieee.numeric_std.all ;
use ieee.std_logic_textio.all ;

entity test_sm is
end test_sm;



architecture testbench of test_sm is

    constant nop_op     : std_logic_vector := "00000000000000000000000000000000";
    constant ctrl_op    : std_logic_vector := "00010000000000000000000000000000";
    constant wt_wd_op   : std_logic_vector := "00100000000000000000000000000000";
    constant wt_blk_op  : std_logic_vector := "00110000000000000000000000000000";
    constant rd_wd_op   : std_logic_vector := "01000000000000000000000000000000";
    constant illegal_op : std_logic_vector := "11110000000000000000000000000000";

    procedure nop (signal op: out std_logic_vector (31 downto 0)) is
    begin
        op <= nop_op after 5 ns;
    end nop;

    procedure ill_op (signal op: out std_logic_vector (31 downto 0)) is
    begin
    	op <= illegal_op after 5 ns;
    end ill_op;

    procedure ctrl (constant  ctl :  in integer;
                      signal   clock : in std_logic;
    	    	      signal     op : out std_logic_vector(31 downto 0)) is
    	variable tmp  :  std_logic_vector(31 downto 0);
    begin
        op <= ctrl_op;
   
        tmp := std_logic_vector(to_unsigned(ctl,32));
        wait until clock = '1';
        op <= tmp after 5 ns;
    end ctrl;

    procedure wt_wd (constant  addr, data  : in integer;
    	    	     signal clock : in std_logic;
                     signal  op   : out std_logic_vector(31 downto 0)) is
    	variable tmp : std_logic_vector(31 downto 0);
    begin
        op <= wt_wd_op  after 5 ns;
        tmp := std_logic_vector(to_unsigned(addr, 32));
        wait until clock'event and clock = '1';
        op <= tmp after 5 ns;
    	tmp := std_logic_vector(to_unsigned(data, 32));
        wait until clock'event and clock = '1';
        op <= tmp after 5 ns; 
    end wt_wd;

    procedure wt_blk (constant addr, data  : in integer;
                      signal clock : in std_logic;
    	    	        signal  op   : out std_logic_vector(31 downto 0)) is
        variable tmp : std_logic_vector(31 downto 0);
        variable dat : integer := data;
    begin
    	 op <= wt_blk_op  after 5 ns;
    	 wait until clock'event and clock = '1';
    	 tmp := std_logic_vector(to_unsigned(addr, 32));
        op <= tmp  after 5 ns;

        for I in 1 to 4 loop
            wait until clock'event and clock = '1';
            tmp := std_logic_vector(to_unsigned(dat,32));
    	     op  <= tmp  after 5 ns;
            dat := dat + 1;
        end loop;
	
    end wt_blk;

    procedure rd_wd (constant  addr   : in integer;
    	    	        signal  clock  : in std_logic;
                       signal  op     : out std_logic_vector(31 downto 0)) is
    	 variable tmp : std_logic_vector(31 downto 0);
    begin
        op <= rd_wd_op  after 5 ns;
        wait until clock'event and clock = '1';
        tmp := std_logic_vector(to_unsigned(addr,32));
        op <= tmp after 5 ns;
    	 wait until clock'event and clock = '1';
        op <= nop_op after 5 ns;
    end rd_wd;

component sm_seq
    port(into 	: in  std_logic_vector(31 downto 0);
         outof	: out std_ulogic_vector(31 downto 0);
		 addr   : out std_ulogic_vector(9 downto 0);
		 data   : inout std_logic_vector(31 downto 0);
         clk	: in  std_ulogic;
		 reset  : in  std_ulogic;
		 rd_n   : out std_ulogic;
		 wr_n   : out std_ulogic
	) ;
end component; 

component sm_sram
  port ( clk : in  std_ulogic ;
         data : inout std_logic_vector(31 downto 0);
         addr : in std_ulogic_vector(9 downto 0);
         rd_n, wr_n : in std_ulogic ) ;
end component;

   for all : sm_seq use entity work.sm_seq(rtl);
   for all : sm_sram use entity work.sm_sram(behav);

     
   signal into  : std_logic_vector(31 downto 0) := (others => '0');
   signal outof : std_ulogic_vector(31 downto 0);
   signal data  : std_logic_vector(31 downto 0);
   signal addr  : std_ulogic_vector(9 downto 0);
   signal clk   : std_ulogic := '0';
   signal reset : std_ulogic := '0';
   signal rd_n, wr_n : std_ulogic := '1';
   signal done,enb_outof  : boolean   := FALSE;

   constant PERIOD  : Time := 20 ns;

begin

    DUT : sm_seq port map (into, outof, addr, data, 
                          clk, reset, rd_n, wr_n);

    RAM : sm_sram port map (clk, data, addr, rd_n, wr_n);
    
    test: process
    begin
       wait until clk'event and clk = '1';
       wait until clk'event and clk = '1';
       wait until clk'event and clk = '1';   -- delay for 3 clks to init.
       enb_outof <= TRUE;                    -- enable outof reads
       for cnt in 1 to 40000 loop
         wait until clk'event and clk = '1';
--           ctrl  ( 5, clk, into );
	 wait until clk'event and clk = '1';
	 wt_wd ( 16#10#, 16#aa#, clk, into );
	 wait until clk'event and clk = '1';
	   wt_wd ( 16#20#, 16#bb#, clk, into );
	 wait until clk'event and clk = '1';	
	   wt_blk ( 16#30#, 16#cc#, clk, into );
	 wait until clk'event and clk = '1';   -- Perform back-to-back reads
	 rd_wd ( 16#10#, clk, into );
	 wait until clk'event and clk = '1';   
		 rd_wd ( 16#20#, clk, into );
	 wait until clk'event and clk = '1';
	 rd_wd ( 16#30#, clk, into );
	 wait until clk'event and clk = '1';
	 rd_wd ( 16#31#, clk, into );
	 wait until clk'event and clk = '1';
	 rd_wd ( 16#32#, clk, into );
	 wait until clk'event and clk = '1';
	 rd_wd ( 16#33#, clk, into );
	 wait until clk'event and clk = '1';	
	 ill_op ( into );
	 wait until clk'event and clk = '1';	
	 nop ( into );
         wait until clk'event and clk = '1';
       end loop;
       wait for PERIOD*3;                    -- delay for 3 clks to stop.
       done <= TRUE;

   end process test;

   clkk : process
   begin
       while (not done) loop
           clk <= '0','1' after PERIOD/2;
           wait for PERIOD;
       end loop;
       wait;
   end process clkk;

   reset <= '1', '0' after 20 ns;


   RD_OUTOF: process (outof)
       variable msg_line : line;
       variable msg1     : string(1 to 10) := "  outof = ";
       variable rd_data  : std_ulogic_vector(31 downto 0);
   begin
       if (enb_outof) then
           rd_data := outof;
           write(msg_line,NOW,field=>10);
           write(msg_line,msg1);
           hwrite(msg_line,rd_data);
           writeline(OUTPUT,msg_line);
       end if;
   end process RD_OUTOF;
       

end testbench;

configuration sm_config of test_sm is
for testbench
end for;
end sm_config;
