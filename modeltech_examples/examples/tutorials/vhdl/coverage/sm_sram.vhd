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
use ieee.numeric_std.all;

entity sm_sram is
  port ( clk : in std_ulogic;
         data : inout std_logic_vector(31 downto 0);
		 addr : in std_ulogic_vector(9 downto 0);
		 rd_n, wr_n : in std_ulogic );
end sm_sram;

architecture behav of sm_sram is
constant Tpd : time := 9 ns;
type mem_t is array(0 to 1023) of std_logic_vector(31 downto 0);
begin

process(clk)
  variable mem : mem_t;
  variable L : line;
begin
  if (clk = '0') then
    if (rd_n = '1' or wr_n = '1') then
	  if ( rd_n = '0') then
	    data <= mem(to_integer(unsigned(addr))) after Tpd;
	  else
	    data <= (others => 'Z') after Tpd;
	  end if;
	  if ( wr_n = '0') then
	    mem(to_integer(unsigned(addr))) := data;
	  end if;
	elsif (rd_n = '0' and wr_n = '0') then
	  write(L, string'("*SRAM* Error: Simultaneous read and write!"));
	  writeline(output,L);
	end if;
  end if;
end process;

end behav;


