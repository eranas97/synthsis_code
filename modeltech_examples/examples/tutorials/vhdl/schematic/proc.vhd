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
entity proc is
  generic (addr_size : Natural := 8;
           word_size : Natural := 16);
  port (clk    : IN     std_ulogic;
        addr   : OUT    std_logic_vector(addr_size-1 downto 0);
        data   : INOUT  std_logic_vector(word_size-1 downto 0);
        rw     : BUFFER std_ulogic;
        strb   : BUFFER std_ulogic;
        rdy    : IN     std_ulogic );
end entity proc;

library IEEE;
  use IEEE.numeric_std.all;
  use IEEE.std_logic_textio.all;
  use STD.textio.all;
  use work.std_logic_util.all;
architecture RTL of proc is
  signal addr_r    : std_logic_vector(addr_size-1 downto 0) := (others => '0');
  signal data_r    : std_logic_vector(word_size-1 downto 0) := (others => 'Z');
  signal rw_r      : std_ulogic := '0';
  signal strb_r    : std_ulogic := '1';
  signal verbose   : Boolean := TRUE;
  signal t_out     : std_ulogic;
  signal t_set     : std_ulogic;
  signal rw_out    : std_ulogic;
  signal test      : std_ulogic := 'X';
  signal test2     : std_ulogic;
  signal bar_rw    : std_ulogic;
  signal test_in   : std_ulogic;
  signal im0       : std_ulogic;
  
  component v_and2 IS
    PORT (
        y  : OUT std_ulogic;
        i1 : IN  std_ulogic;
        i0 : IN  std_ulogic
    );
  END component v_and2;
  
  component and2 is
    port (a, b : IN  std_ulogic;
          y    : OUT std_ulogic );
  end component and2;
  
  component or2 is
    port (a, b : IN  std_ulogic;
          y    : OUT std_ulogic);
  end component or2;
  
 begin
   addr <= addr_r after 5 ns;
   data <= data_r after 5 ns;
   rw   <= rw_r   after 5 ns;
   strb <= strb_r after 5 ns;
   bar_rw <= not rw;
   
   i0 : and2 port map( y => test, a => rw, b => test2 );

   test2_asgn: test2 <= bar_rw or test_in;
   t_out_asgn: t_out <= test nand strb;

  process
    variable a : std_logic_vector(addr_size-1 downto 0);
    variable d : std_logic_vector(word_size-1 downto 0);
    variable a_str : LINE;
    variable d_str : LINE;
    
    procedure write ( a : std_logic_vector(addr_size-1 downto 0);
                      d : std_logic_vector(word_size-1 downto 0) )
    is
      variable d_str, a_str : LINE;
    begin
      if (verbose) then
         write(d_str, d);
         write(a_str, a);
         report time'image(now) & ": Writing data=" & d_str.all &
                                  " to addr=" & a_str.all;
         deallocate(d_str);
         deallocate(a_str);
      end if;
      addr_r <= a;
      rw_r <= '0';
      strb_r <= '0';
      wait until clk'event and clk = '1';
      strb_r <= '1';
      data_r <= d;
      wait until clk'event and clk = '1';
      while (rdy /= '0') loop
        wait until clk'event and clk = '1';
      end loop;
      data_r <= (others => 'Z');
    end procedure write;

    procedure read ( a : std_logic_vector(addr_size-1 downto 0);
                     d : out std_logic_vector(word_size-1 downto 0) )
    is
      variable a_str : LINE;
    begin
      if (verbose) then
        write(a_str, a);
        report time'image(now) & ": Reading from addr=" & a_str.all;
        deallocate(a_str);
      end if;
      addr_r <= a;
      rw_r <= '1';
      strb_r <= '0';
      wait until clk'event and clk = '1';
      strb_r <= '1';
      wait until clk'event and clk = '1';
      while (rdy /= '0') loop
        wait until clk'event and clk = '1';
      end loop;
      d := data;
    end procedure read;    

  begin
    while (TRUE) loop
      -- Wait for first clock, then perform read/write test
      wait until clk'event and clk = '1';
      if (verbose) then
        report time'image(now) & ": Starting Read/Write test";
      end if;

      -- Write 10 locations
      for i in 0 to 9 loop
        a := std_logic_vector(to_unsigned(i, a'length));
        if word_size > addr_size then
          d(word_size-1 downto addr_size) := (others => '0');
          d(addr_size-1 downto 0) := a;
          write(a, d);
        else
          write(a, a(word_size-1 downto 0));
        end if;
      end loop;

      -- Read back 10 locations
       for i in 0 to 9 loop
         read(a, d);
         if ((word_size < addr_size) and (d /= a(word_size-1 downto 0))) or
            ((addr_size <= word_size) and (d(addr_size-1 downto 0) /= a))
         then
           write(a_str, a);
           write(d_str, d);
           report time'image(now) & ": Read/Write mismatch; E:" &
                                    a_str.all & " A: " & d_str.all;
           deallocate(a_str);
           deallocate(d_str);
         end if;
       end loop;

       if (verbose) then
         report "Read/Write test done";
         stop <= TRUE;
         wait;
       end if;
    end loop;
  end process;
    
  i1 : or2 port map (y=>t_set, a=>t_out, b=>im0);

  i2 : v_and2 port map (y=>im0, i0=>'0', i1=>'1');

  rw_out <= t_set when (rw_r = '1') else 'Z';
    
end architecture rtl;
