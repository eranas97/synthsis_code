--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

library IEEE ;
use IEEE.std_logic_1164.all ;
use ieee.numeric_std.all ;

entity sm_seq is
    port(into 	: in  std_logic_vector(31 downto 0);
         outof	: out std_ulogic_vector(31 downto 0);
		 addr   : out std_ulogic_vector(9 downto 0);
		 data   : inout std_logic_vector(31 downto 0);
         clk	: in  std_ulogic;
		 reset  : in  std_ulogic;
		 rd_n   : out std_ulogic;
		 wr_n   : out std_ulogic
	) ;
end sm_seq; 




architecture  rtl of sm_seq  is
--
-- Propagation Delay for all registers
--
	constant Tpd : time := 5 ns ;
--
-- Register declarations
--
	signal in_reg 	: std_ulogic_vector(31 downto 0) ;
	signal w_data	: std_ulogic_vector(31 downto 0) ;
	signal r_data	: std_ulogic_vector(31 downto 0) ;
	signal ctrl_reg	: std_ulogic_vector(7 downto 0) ;
--
-- Create an alias for the opcode and address bits
--
	alias opcode_bits : std_ulogic_vector(3 downto 0) is in_reg(31 downto 28) ;
	alias addr_bits   : std_ulogic_vector(9 downto 0) is in_reg(9 downto 0);
--
-- Enable Signals
--
	signal a_wen  : std_ulogic ;
	signal wd_wen : std_ulogic ;
	signal rd_wen : std_ulogic ;
	signal inca   : std_ulogic ;
        signal ctrl_wen : std_ulogic;

    signal wr_s : std_ulogic := '1';
	signal addr_s : std_ulogic_vector(9 downto 0);

  component sm
    port (clk : in std_ulogic;
          reset : in std_ulogic;
          opcode : in std_ulogic_vector(3 downto 0);
	  	  a_wen : out std_ulogic;
		  wd_wen : out std_ulogic;
		  rd_wen : out std_ulogic;
                  ctrl_wen : out std_ulogic;
		  inca   : out std_ulogic );
  end component;

  for all : sm use entity work.sm(rtl);


begin

FSM : sm port map (clk, reset, opcode_bits,
                   a_wen, wd_wen, rd_wen, ctrl_wen, inca );

rd_n <= rd_wen;
wr_n <= wr_s;
addr <= addr_s;
data <= std_logic_vector(w_data) when wr_s = '0' else (others => 'Z');

registers:
  process(clk)
        variable addr_v : natural := 0;
	begin	  
	  if (clk'event and clk='1') then
	    if (reset = '1') then

		  in_reg <= std_ulogic_vector(into) after Tpd;
		  outof <= r_data after Tpd;
		  addr_s <= addr_bits after Tpd;
		  w_data <= in_reg after Tpd;
		  wr_s <= '1';
		  r_data <= std_ulogic_vector(data) after Tpd;
                  ctrl_reg <= (others => '0') after Tpd;

		else

		-- Load in_reg register
			in_reg <= std_ulogic_vector(into) after Tpd ;

		-- Load r_data register
			if (rd_wen = '0') then
				r_data <= std_ulogic_vector(data) after Tpd ;
			end if ;

		-- Load outof register
			outof  <= r_data after Tpd ;

            wr_s <= wd_wen after Tpd;

		-- Load addr register
			if (a_wen = '0') then
				addr_s <= addr_bits after Tpd ;
                                addr_v := to_integer(unsigned(addr_bits));
			elsif (inca = '1') then
                                addr_v := addr_v + 1;
				addr_s <= std_ulogic_vector(to_unsigned(addr_v, addr_s'length)) after Tpd;
			end if ;

		-- Load w_data register	
			if (wd_wen = '0') then
				w_data <= in_reg after Tpd;
			end if ;

                -- Load ctrl register
                        if (ctrl_wen = '0') then
                                ctrl_reg <= in_reg(7 downto 0) after Tpd;
                        end if;
		end if;	 -- reset
	end if ;  -- clk
  end process ;

end rtl;





















