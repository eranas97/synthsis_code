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

entity traffic is
  port (
        car_ns : in std_logic;
        car_ew : in std_logic;

        light_ns : out std_logic_vector (2 downto 0);
        light_ew : out std_logic_vector (2 downto 0);

        ns_green_time  : TIME := 30 ns;	-- minimum time for 
					--  north/south green light
        ew_green_time  : TIME := 30 ns;	-- minimum time for 
					--  east/west green light
        ns_yellow_time : TIME :=  3 ns;	-- total time for 
					--  north/south yellow light
        ew_yellow_time : TIME :=  3 ns;	-- total time for 
					--  east/west yellow light
        both_red_time  : TIME :=  1 ns	-- total time for 
					--  east/west yellow light
        );
end traffic;

architecture simple of traffic is
  type traffic_state is (
		ns_green, ew_green, 
		both_red, 
		ns_yellow, ew_yellow);

  signal curr_st       : traffic_state := ns_green;
  signal next_st       : traffic_state := ns_green;
  signal last_green_st : traffic_state := ns_green;
  signal curr_st_time  : TIME := 0 ns;

begin  --  simple

light_gen : process (curr_st)
  
begin  --  process light_gen 

  case curr_st is

    when both_red =>
      light_ns <= "100";
      light_ew <= "100";

    when ns_green =>
      light_ns <= "001";
      light_ew <= "100";

    when ew_green =>
      light_ns <= "100";
      light_ew <= "001";

    when ns_yellow =>
      light_ns <= "010";
      light_ew <= "100";

    when ew_yellow =>
      light_ns <= "100";
      light_ew <= "010";

  end case;                              --  curr_st
end process light_gen;


fsm : process 

begin  --  process fsm 

    case curr_st is

      when ns_green =>
        last_green_st <= ns_green;
        if (car_ew /= '0') then
          curr_st <= ns_yellow;
          wait for ns_yellow_time;
        else
          wait on car_ew;
        end if;

      when ns_yellow | ew_yellow =>
        curr_st <= both_red;
        wait for both_red_time;

      when both_red =>
        if (last_green_st = ns_green) then
          curr_st <= ew_green;
          wait for ns_green_time;
        else
          curr_st <= ns_green;
          wait for ew_green_time;
        end if;

      when ew_green =>
        last_green_st <= ew_green;
        if (car_ns /= '0') then
          curr_st <= ew_yellow;
          wait for ew_yellow_time;
        else
          wait on car_ns;
        end if;

    end case;                           --  curr_st
end process fsm;
end simple;
