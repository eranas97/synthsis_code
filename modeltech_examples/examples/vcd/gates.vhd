--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

------------------------------------------------------------------------
-- package with component declarations
------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
package gates is
    component andg
	generic (tpd_hl : time := 1 ns;
		 tpd_lh : time := 1 ns);
	port (in1, in2 : std_ulogic;
	      out1 : out std_ulogic);
    end component;  
    component org
	generic (tpd_hl : time := 1 ns;
		 tpd_lh : time := 1 ns);
	port (in1, in2 : std_logic;
	      out1 : out std_logic);
    end component;  
    component xorg
	generic (tpd_hl : time := 1 ns;
		 tpd_lh : time := 1 ns);
	port (in1, in2 : std_logic;
	      out1 : out std_logic);
    end component;  
end gates;

------------------------------------------------------------------------
-- and gate
------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
entity andg is
    generic (tpd_hl : time := 1 ns;
	     tpd_lh : time := 1 ns);
    port (in1, in2 : std_ulogic;
	  out1 : out std_ulogic);
end andg;

architecture only of andg is
begin
    p1: process(in1, in2)
        variable val : std_logic;
    begin
	val := in1 and in2;
	case val is 
	    when '0' =>
		out1 <= '0' after tpd_hl;
	    when '1' =>
		out1 <= '1' after tpd_lh;
	    when others =>
		out1 <= val;
	end case;
    end process;
end only;

------------------------------------------------------------------------
-- or gate
------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;

entity org is
    generic (tpd_hl : time := 1 ns;
	     tpd_lh : time := 1 ns);
    port (in1, in2 : std_logic;
	  out1 : out std_logic);
end org;
architecture only of org is
begin
    p1: process(in1, in2)
        variable val : std_logic;
    begin
	val := in1 or in2;
	case val is 
	    when '0' =>
		out1 <= '0' after tpd_hl;
	    when '1' =>
		out1 <= '1' after tpd_lh;
	    when others =>
		out1 <= val;
	end case;
    end process;
end only;

------------------------------------------------------------------------
-- exclusive or gate
------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;

entity xorg is
    generic (tpd_hl : time := 1 ns;
	     tpd_lh : time := 1 ns);
    port (in1, in2 : std_logic;
	  out1 : out std_logic);
end xorg;
architecture only of xorg is
begin
    p1: process(in1, in2)
        variable val : std_logic;
    begin
	val := in1 xor in2;
	case val is 
	    when '0' =>
		out1 <= '0' after tpd_hl;
	    when '1' =>
		out1 <= '1' after tpd_lh;
	    when others =>
		out1 <= val;
	end case;
    end process;
end only;

