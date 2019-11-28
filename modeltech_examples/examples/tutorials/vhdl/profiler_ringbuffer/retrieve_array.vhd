--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

-- Produces the output pointer logic.

library ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.std_logic_unsigned.all;

ENTITY retrieve IS
   GENERIC (
      counter_size : integer := 8;
      buffer_size : integer := 256
   );
   PORT (
      outstrobe : IN std_logic;
      ramadrs : IN std_logic_vector((counter_size * 2) DOWNTO 0);
      buffers : IN std_logic_vector((buffer_size -1) DOWNTO 0);
      rxda : OUT std_logic
   );
END retrieve;

ARCHITECTURE RTL OF retrieve IS
  signal rd0a : std_logic;
BEGIN

-- Produces the decode logic which pointers
-- to each location of the shift register.
retriever : PROCESS (buffers,ramadrs((counter_size-1) downto 0))
  variable address : integer range 0 to (buffer_size-1);
BEGIN
  address := conv_integer(ramadrs((counter_size-1) downto 0));
  rd0a <= buffers(address);
END PROCESS;

rxda <= rd0a and outstrobe;

END RTL;
