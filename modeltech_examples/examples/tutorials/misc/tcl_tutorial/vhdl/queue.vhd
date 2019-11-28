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

entity queue is
  generic (departure_rate : time := 5 ns);
  port (is_empty     : out std_logic;
        consume      : in  std_logic;
        arrival_rate : time
       );
end queue;

architecture only of queue is
  signal current_count : integer := 0;

begin  --  only 

  queue_ctl : process(current_count,consume)
  begin

    current_count <= current_count + 1 after arrival_rate;
    if(consume = '1') then
	if(current_count > 0) then
	  current_count <= current_count - 1 after departure_rate;
	end if;
    end if;
  end process queue_ctl;

  empty : process (current_count)
  begin

    if (current_count = 0) then
      is_empty <= '1';
    else
      is_empty <= '0';
    end if;
  end process empty;

end only;

