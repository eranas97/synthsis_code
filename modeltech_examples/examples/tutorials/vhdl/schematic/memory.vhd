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
entity memory is
  generic ( addr_size : Natural := 8;
            word_size : Natural := 16 );
  port (clk   : IN    std_ulogic;
        addr  : IN    std_logic_vector(addr_size-1 downto 0);
        data  : INOUT std_logic_vector(word_size-1 downto 0);
        rw    : IN    std_ulogic;
        strb  : IN    std_ulogic;
        rdy   : OUT   std_ulogic );
end entity memory;

library IEEE;
  use IEEE.numeric_std.all;
architecture RTL of memory is

  signal data_r : std_logic_vector(word_size-1 downto 0) := (others => 'Z');
  signal rdy_r  : std_ulogic := '1';
  subtype mem_word is std_logic_vector(word_size-1 downto 0);
  type mem_type is array(0 to (2**addr_size-1)) of mem_word;
  shared variable mem : mem_type;

begin

  data <= data_r after 5 ns;
  rdy  <= rdy_r  after 5 ns;

  process
    variable i : integer;
  begin
    wait until clk'event and clk = '1';
    if (strb = '0') then
      i := to_integer(unsigned(addr));
      wait until clk'event and clk = '1';
      wait until clk'event and clk = '1';
      if (rw = '1') then
        data_r <= mem(i);
      end if;
      rdy_r <= '0';
      wait until clk'event and clk = '1';
      rdy_r <= '1';
      if (rw = '0') then
        mem(i) := data;
      else
        data_r <= (others => 'Z');
      end if;
    end if;
  end process;
  
end architecture RTL;
