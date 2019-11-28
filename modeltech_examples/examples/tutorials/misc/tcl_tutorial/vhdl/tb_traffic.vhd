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

entity tb_traffic is
end tb_traffic;

architecture only of tb_traffic is
  component traffic
    port (
        car_ns : in std_logic;
        car_ew : in std_logic;

        light_ns : out std_logic_vector (2 downto 0);
        light_ew : out std_logic_vector (2 downto 0);

        ns_green_time  : TIME;
        ew_green_time  : TIME;
        ns_yellow_time : TIME;
        ew_yellow_time : TIME;
        both_red_time  : TIME
        );
  end component;

  component queue
    generic (departure_rate : time := 5 ns);
    port (is_empty     : out std_logic;
          consume      : in  std_logic;
          arrival_rate : in  time
       );
  end component;

  signal car_ew : std_logic;
  signal car_ns : std_logic;

  signal light_ew : std_logic_vector (2 downto 0);
  signal light_ns : std_logic_vector (2 downto 0);

  signal queue_e_empty, 
	 queue_w_empty, 
	 queue_n_empty, 
	 queue_s_empty : std_logic;

  signal pass_ns, 
	 pass_ew : std_logic;

  signal       ns_green_time  : TIME := 30 ns;
  signal       ew_green_time  : TIME := 30 ns;
  signal       ns_yellow_time : TIME := 5 ns;
  signal       ew_yellow_time : TIME := 5 ns;
  signal       both_red_time  : TIME := 2 ns;

  signal ns_arrival_rate : TIME := 40 ns;
  signal ew_arrival_rate : TIME := 40 ns;

  signal clock : std_logic;

begin  --  only

  tick : process
    begin
      clock <= '1';
      wait for 1 ns;
      clock <= '0';
      wait for 1 ns;
    end process tick;

  pass_ew <= light_ew(0);
  pass_ns <= light_ns(0);

  -----------------------------------------------------------------------------
  --  generate the car waiting signals
  -----------------------------------------------------------------------------
  car_ew <= not(queue_e_empty) or not(queue_w_empty);
  car_ns <= not(queue_n_empty) or not(queue_s_empty);

  -----------------------------------------------------------------------------
  --  instantiate traffic arrival queues
  -----------------------------------------------------------------------------
  queue_e : queue port map (queue_e_empty, pass_ew, ew_arrival_rate);
  queue_w : queue port map (queue_w_empty, pass_ew, ew_arrival_rate);

  queue_n : queue port map (queue_n_empty, pass_ns, ns_arrival_rate);
  queue_s : queue port map (queue_s_empty, pass_ns, ns_arrival_rate);

  -----------------------------------------------------------------------------
  --  instantiate traffic controller
  -----------------------------------------------------------------------------
  traffic_light : traffic port map (car_ns, car_ew,
				light_ns, light_ew,
				ns_green_time,
				ew_green_time,
				ns_yellow_time,
				ew_yellow_time,
				both_red_time);

end only;
