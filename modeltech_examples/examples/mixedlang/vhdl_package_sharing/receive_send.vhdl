--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--

use work.common_vh_pack.all;

entity receive_send is
	port (  clk : in bit;
			data_received : in vh_arr;
			data_sent : out vh_arr);
end receive_send;

architecture arch_receive_send of receive_send is
begin
	process (data_received)
	begin
		data_sent <= data_received;
	end process;
end arch_receive_send;
