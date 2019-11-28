--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

-- This block produces the address generation
-- and strobe generation for input and output
-- data.
-- 

library ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.std_logic_unsigned.all;

ENTITY control IS
   GENERIC (
      counter_size : integer := 4
   );
   PORT (
      clock	: IN std_logic;
      reset	: IN std_logic;
      ramadrs : OUT std_logic_vector((counter_size * 2) DOWNTO 0);
      oeenable : OUT std_logic;
      outstrobe : OUT std_logic;
      txc : OUT std_logic;
      wrb : in std_logic;
      csb : in std_logic;
      switch : in std_logic_vector(3 DOWNTO 0);
      txd : in std_logic_vector(3 DOWNTO 0);
      buffer_txd : out std_logic;
      rxd : out std_logic_vector(3 DOWNTO 0);
      buffer_rxd : in std_logic;
      monitor_activity : out std_logic_vector(7 DOWNTO 0)
   );
END control;

ARCHITECTURE RTL OF control IS
  signal address: std_logic_vector((counter_size * 2) DOWNTO 0);
  signal control_reg : std_logic_vector(3 DOWNTO 0);
  signal monitor : std_logic_vector(7 DOWNTO 0);
  signal rxd_active : std_logic;
BEGIN

-- This block stores the data switching
Register_control_data : PROCESS (wrb,reset)
BEGIN
  IF reset = '0' THEN
    control_reg <= "1111";
  ELSIF (wrb'event AND wrb = '1') THEN
    IF csb = '0' THEN
      control_reg <= switch;
    END IF;
  END IF;
END PROCESS;

-- This block switches data
Switch_data : PROCESS (control_reg,txd,buffer_rxd)
BEGIN
  case control_reg(1 downto 0) is 
    when "11"  => buffer_txd <= txd(0);
    when "10"  => buffer_txd <= txd(1);
    when "01"  => buffer_txd <= txd(2);
    when "00"  => buffer_txd <= txd(3);
    when others => buffer_txd <= 'X';
  end case;
  case control_reg(3 downto 2) is 
    when "11"  => rxd <= buffer_rxd & "111";
                  rxd_active <= buffer_rxd;
    when "10"  => rxd <= '1' & buffer_rxd & "11";
                  rxd_active <= '1';
    when "01"  => rxd <= "11" & buffer_rxd & '1';
                  rxd_active <= '1';
    when "00"  => rxd <= "111" & buffer_rxd ;
                  rxd_active <= '1';
    when others => rxd <= "XXXX"; rxd_active <= 'X';
  end case;
END PROCESS;

-- This block creates an N-bit counter
Incrementer : PROCESS (clock)
BEGIN
  IF (clock'event AND clock = '1') THEN
    IF reset = '0' THEN
      address <= (others => '0');
    ELSE
      address <= address + '1';
    END IF;
  END IF;
END PROCESS;

-- This block generates the oeenable strobe used by the data store
Enable_gen : PROCESS (clock)
BEGIN
  IF (clock'event AND clock = '1') THEN
    IF reset = '0' THEN
      oeenable <= '0';
    ELSIF (address(counter_size DOWNTO 0) = 0) THEN
      oeenable <= '1';
    ELSE
      oeenable <= '0';
    END IF;
  END IF;
END PROCESS;

-- This block implements the outstrobe
-- signal that is used to show when data output by the 
-- device is valid 
OutStrobe_gen : PROCESS (address)
  variable x : std_logic;
BEGIN
  x := '1';
  for i in counter_size to (counter_size * 2) loop
    x := x and address(i);
  end loop ;
  outstrobe <= x;
END PROCESS;

-- This block Monitors Activity on RXDA
Activity_monitor : PROCESS (rxd_active,Reset)
BEGIN
  IF reset = '0' THEN
    monitor <= (others => '0');
  ELSIF (rxd_active'event AND rxd_active = '0') THEN
    monitor <= monitor + '1';
  END IF;
END PROCESS;

monitor_activity <= monitor;
ramadrs <= address;
txc <= address(counter_size);

END RTL;










