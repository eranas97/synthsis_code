--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

library IEEE;
use IEEE.std_logic_1164.all;

entity sm is
  port (clk : in std_ulogic;
        reset : in std_ulogic;
        opcode : in std_ulogic_vector(3 downto 0);
	a_wen : out std_ulogic;
	wd_wen : out std_ulogic;
	rd_wen : out std_ulogic;
        ctrl_wen : out std_ulogic;
	inca   : out std_ulogic );
end sm;



architecture  rtl of sm  is
--
-- Opcodes 
--
	constant nop    : std_ulogic_vector(3 downto 0) := "0000" ;
	constant ctrl_op : std_ulogic_vector(3 downto 0) := "0001" ;
	constant wt_wd  : std_ulogic_vector(3 downto 0) := "0010" ;
	constant wt_blk : std_ulogic_vector(3 downto 0) := "0011" ;
	constant rd_wd  : std_ulogic_vector(3 downto 0) := "0100" ;
--
-- State names and state varaible declarations
--
	type state_names is (	idle,

				wt_wd_1, 
				wt_wd_2,

				wt_blk_1,
				wt_blk_2,
				wt_blk_3,
				wt_blk_4,
				wt_blk_5,

				rd_wd_1,
				rd_wd_2,
                                ctrl
			) ;

	signal state, next_state : state_names ;

begin

next_state_var:
	process(clk)
	begin
	if (clk'event and clk='1') then
          if (reset = '1') then
            state <= idle;
          else
	    state <= next_state;
          end if;
	end if ;
	end process ;

comb_decoding:
	process(state, opcode)
	begin
--
-- Set default values for all outputs
--
	a_wen  <= '1' ;
	wd_wen <= '1' ;
	rd_wen <= '1' ;
        ctrl_wen <= '1';
	inca <= '0' ;
--
-- Next state and output decoding logic
--		
		case (state) is
			when idle => case opcode is
					when nop  	=> next_state <= idle ;
                                        when ctrl_op    => next_state <= ctrl;
					when wt_wd	=> next_state <= wt_wd_1 ;
					when wt_blk	=> next_state <= wt_blk_1 ;
					when rd_wd	=> next_state <= rd_wd_1 ;
					when others	=> next_state <= idle ;
							   assert (false)
								report "Illegal Opcode"
								severity note ;
				    end case ;

                        when ctrl       => next_state <= idle;
                                           ctrl_wen <= '0';
			when wt_wd_1	=> next_state <= wt_wd_2 ;
					   a_wen <= '0' ;
			when wt_wd_2	=> next_state <= idle ;
					   wd_wen <= '0' ;

			when wt_blk_1	=> next_state <= wt_blk_2 ;
					   a_wen <= '0' ;
			when wt_blk_2	=> next_state <= wt_blk_3 ;
					   wd_wen <= '0' ;
			when wt_blk_3	=> next_state <= wt_blk_4 ;
					   wd_wen <= '0' ;
					   inca <= '1' ;
			when wt_blk_4	=> next_state <= wt_blk_5 ;
					   wd_wen <= '0' ;
					   inca <= '1' ;
			when wt_blk_5	=> next_state <= idle ;
					   wd_wen <= '0' ;
					   inca <= '1' ;

			when rd_wd_1	=> next_state <= rd_wd_2 ;
					   a_wen <= '0' ;
			when rd_wd_2	=> next_state <= idle ;
					   rd_wen <= '0' ;

			when others 	=> next_state <= idle ;
					   assert (false) 
						report "Illegal state"
						severity warning ;
		end case;
	end process ;

end rtl;
