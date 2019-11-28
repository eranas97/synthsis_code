--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--

use work.common_vl_pack.all;

entity receive_send is
	generic (   untyped_param : integer := 0;
				bit_param : bit := '0';
				string_param : string := "receive_send";
				array_type_param : vl_array := "0110");
	port (  clk : in bit;
			data_received : in vl_rec;
			data_sent : out vl_rec);
end receive_send;

architecture arch_receive_send of receive_send is
begin
	process (data_received)
	begin
		report "untyped_param = " & integer'image(untyped_param);
		report "bit_param = " & bit'image(bit_param);
		report "string_param = " & string_param;
		report "array_type_param = " & bit'image(array_type_param(3)) & bit'image(array_type_param(2)) & bit'image(array_type_param(1)) & bit'image(array_type_param(0));
		data_sent.vl_bit <= data_received.vl_bit;
		for index in 3 downto 0 loop
			data_sent.vl_arr(index) <= data_received.vl_arr(index);
		end loop;
	end process;
end arch_receive_send;
