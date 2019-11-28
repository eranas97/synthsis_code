--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--

use work.common_vl_pack.all;

entity send_receive is
end send_receive;

architecture arch_send_receive of send_receive is
	component receive_send is
		generic (   bit_generic : bit := '0';
					string_generic : string := "receive_send";
					array_type_generic : vl_array := "0110");
		port (data_received : in vl_rec);
	end component;
	signal clk : bit;
	signal data_sent : vl_rec := ('0', "0000");
begin
	clk <= not clk after 5 ns;

	process (clk)
	begin
		data_sent.vl_bit <= not data_sent.vl_bit;
		data_sent.vl_arr(0) <= not data_sent.vl_bit;
		data_sent.vl_arr(1) <= not data_sent.vl_arr(0);
		data_sent.vl_arr(2) <= not data_sent.vl_arr(1);
		data_sent.vl_arr(3) <= not data_sent.vl_arr(2);
	end process;

	inst_receive_send : receive_send generic map ('1', "send_receive", "1001") port map (data_sent);
end arch_send_receive;
