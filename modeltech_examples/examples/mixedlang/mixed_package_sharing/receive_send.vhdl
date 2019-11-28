--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--

use work.common_vh_pack.all;
use work.common_vl_pack.all;

entity receive_send is
	port (  clk : in bit;
			data_received : in vh_arr(vl_word_size downto 0);
			data_sent : out vl_arr);
end receive_send;

architecture arch_receive_send of receive_send is
begin
	process (data_received)
	begin
		for index in vl_word_size downto 0 loop
			data_sent(index) <= data_received(index);
		end loop;
	end process;
end arch_receive_send;
