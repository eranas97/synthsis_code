--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

library ieee;
use ieee.std_logic_1164.all;

entity top is end;

use work.std_logic_util.all;
architecture only of top is
	component proc
	    port(
    	    clk             : in     std_logic;
            addr            : out    std_logic_vector(7 downto 0);
    	    data            : inout  std_logic_vector(15 downto 0);
            rw              : BUFFER std_logic;
            strb            : BUFFER std_logic;
    	    rdy             : in     std_logic
	    );
	end component;

	component cache
	    port(
    	    clk             : in    std_logic;
            paddr           : in    std_logic_vector(7 downto 0);
            pdata           : inout std_logic_vector(15 downto 0);
    	    prw             : in    std_logic;
            pstrb           : in    std_logic;
            prdy            : out   std_logic;
    	    saddr           : out   std_logic_vector(7 downto 0);
            sdata           : inout std_logic_vector(15 downto 0);
            srw             : out   std_logic;
    	    sstrb           : out   std_logic;
            srdy            : in    std_logic
	    );
	end component;

	component memory
	    port(
    	    clk             : in    std_logic;
            addr            : in    std_logic_vector(7 downto 0);
            data            : inout std_logic_vector(15 downto 0);
    	    rw              : in    std_logic;
            strb            : in    std_logic;
            rdy             : out   std_logic
    	);
	end component;

    signal clk : std_logic := '0';

    -- Processor bus signals
    signal prw, pstrb, prdy : std_logic;
    signal paddr : std_logic_vector(7 downto 0);
    signal pdata : std_logic_vector(15 downto 0);

    -- System bus signals
    signal srw, sstrb, srdy : std_logic;
    signal saddr : std_logic_vector(7 downto 0);
    signal sdata : std_logic_vector(15 downto 0);
    
begin

    process
    begin
      if stop then
        wait;
      end if;
      clk <= not clk after 20 ns;
      wait on clk;
    end process;

    p: proc   port map(clk, paddr, pdata, prw, pstrb, prdy);

    c: cache  port map(clk, paddr, pdata, prw, pstrb, prdy,
                                        saddr, sdata, srw, sstrb, srdy);

    m: memory port map(clk, saddr, sdata, srw, sstrb, srdy);

end;
