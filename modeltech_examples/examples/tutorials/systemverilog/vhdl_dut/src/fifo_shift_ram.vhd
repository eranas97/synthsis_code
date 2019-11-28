library ieee;
    use ieee.std_logic_1164.all;
    use ieee.std_logic_unsigned.all;
library work;
    use work.all;

entity fifo_shift_ram is
  generic (
     PORTA_MAX_ADDR_SIZE        : NATURAL  :=11;
     BUG                        : integer  :=0
     );
port (
    clk             : in  std_logic;
    reset_n         : in  std_logic;
    push            : in  std_logic_vector (10 downto 0);
    ram_re          : in  std_logic;
    din             : in  std_logic_vector (7 downto 0);
    sel             : in  std_logic_vector (3 downto 0);
    dout            : out std_logic_vector (7 downto 0)
    );

end fifo_shift_ram;

architecture RTL of fifo_shift_ram is

  constant ten_zeros : std_logic_vector(9 downto 0) := (others => '0');

  signal addr    : std_logic_vector(10 downto 0);
  signal addra   : std_logic_vector(10 downto 0);
  signal addrb   : std_logic_vector(10 downto 0);
  signal waddr1  : std_logic_vector(10 downto 0);
  signal waddr2  : std_logic_vector(10 downto 0);
  signal waddr3  : std_logic_vector(10 downto 0);
  signal waddr4  : std_logic_vector(10 downto 0);
  signal waddr5  : std_logic_vector(10 downto 0);
  signal waddr6  : std_logic_vector(10 downto 0);
  signal waddr7  : std_logic_vector(10 downto 0);
  signal waddr8  : std_logic_vector(10 downto 0);
  signal waddr9  : std_logic_vector(10 downto 0);
  signal waddr10 : std_logic_vector(10 downto 0);
  signal waddr11 : std_logic_vector(10 downto 0);
  signal raddr1  : std_logic_vector(10 downto 0);
  signal raddr2  : std_logic_vector(10 downto 0);
  signal raddr3  : std_logic_vector(10 downto 0);
  signal raddr4  : std_logic_vector(10 downto 0);
  signal raddr5  : std_logic_vector(10 downto 0);
  signal raddr6  : std_logic_vector(10 downto 0);
  signal raddr7  : std_logic_vector(10 downto 0);
  signal raddr8  : std_logic_vector(10 downto 0);
  signal raddr9  : std_logic_vector(10 downto 0);
  signal raddr10 : std_logic_vector(10 downto 0);
  signal raddr11 : std_logic_vector(10 downto 0);
  signal add_p1  : std_logic_vector(10 downto 0);
  signal ram_we  : std_logic;

  function bits1 (in_vec : in std_logic_vector (10 downto 0)) return integer is
  variable result : integer := 0;
  begin
    for index in in_vec'range loop
      if (in_vec(index) = '1') then
        result := result + 1;
      end if;
    end loop;
    return result;
  end function bits1;


-- Default assertion clock
-- p sl default clock is rising_edge(clk);

-- Verify that only one level of the RAM is written at a time
-- p sl property push_mutex_check is always {ram_we} |-> { onehot(push); NOT(ram_we)};
-- p sl assert push_mutex_check;

-- p sl property ram_write_check (boolean we, wadd_eq_ram_add, wadd_lowrange, wadd_higrange) is
-- always {we} |-> {wadd_eq_ram_add AND wadd_lowrange AND wadd_higrange; NOT(we) AND wadd_lowrange AND wadd_higrange};

-- p sl assert ram_write_check (push(0),  (addra = waddr1),  (waddr1  >= "00000000000"), (waddr1  <= "00000010000"));
-- p sl assert ram_write_check (push(1),  (addra = waddr2),  (waddr2  >= "00001000000"), (waddr2  <= "00001100001"));
-- p sl assert ram_write_check (push(2),  (addra = waddr3),  (waddr3  >= "00010000000"), (waddr3  <= "00010110010"));
-- p sl assert ram_write_check (push(3),  (addra = waddr4),  (waddr4  >= "00100000000"), (waddr4  <= "00101000011"));
-- p sl assert ram_write_check (push(4),  (addra = waddr5),  (waddr5  >= "00110000000"), (waddr5  <= "00111010100"));
-- p sl assert ram_write_check (push(5),  (addra = waddr6),  (waddr6  >= "01000000000"), (waddr6  <= "01001100101"));
-- p sl assert ram_write_check (push(6),  (addra = waddr7),  (waddr7  >= "01010000000"), (waddr7  <= "01011110110"));
-- p sl assert ram_write_check (push(7),  (addra = waddr8),  (waddr8  >= "01100000000"), (waddr8  <= "01110000111"));
-- p sl assert ram_write_check (push(8),  (addra = waddr9),  (waddr9  >= "10000000000"), (waddr9  <= "10010011000"));
-- p sl assert ram_write_check (push(9),  (addra = waddr10), (waddr10 >= "10100000000"), (waddr10 <= "10110101001"));
-- p sl assert ram_write_check (push(10), (addra = waddr11), (waddr11 >= "11000000000"), (waddr11 <= "11010111010"));

-- Verify that the proper level RAM address is selected
-- and the RAM address is within the acceptable range during a read
-- p sl property ram_read_check (boolean rden, radd_eq_ram_add, radd_lowrange, radd_highrange) is
-- always {(rden AND radd_eq_ram_add)} |-> {radd_lowrange AND radd_highrange; NOT(rden)};

-- p sl assert ram_read_check (ram_re,  (addrb = raddr1),  (raddr1  >= "00000000000"), (raddr1  <= "00000010000"));
-- p sl assert ram_read_check (ram_re,  (addrb = raddr2),  (raddr2  >= "00001000000"), (raddr2  <= "00001100001"));
-- p sl assert ram_read_check (ram_re,  (addrb = raddr3),  (raddr3  >= "00010000000"), (raddr3  <= "00010110010"));
-- p sl assert ram_read_check (ram_re,  (addrb = raddr4),  (raddr4  >= "00100000000"), (raddr4  <= "00101000011"));
-- p sl assert ram_read_check (ram_re,  (addrb = raddr5),  (raddr5  >= "00110000000"), (raddr5  <= "00111010100"));
-- p sl assert ram_read_check (ram_re,  (addrb = raddr6),  (raddr6  >= "01000000000"), (raddr6  <= "01001100101"));
-- p sl assert ram_read_check (ram_re,  (addrb = raddr7),  (raddr7  >= "01010000000"), (raddr7  <= "01011110110"));
-- p sl assert ram_read_check (ram_re,  (addrb = raddr8),  (raddr8  >= "01100000000"), (raddr8  <= "01110000111"));
-- p sl assert ram_read_check (ram_re,  (addrb = raddr9),  (raddr9  >= "10000000000"), (raddr9  <= "10010011000"));
-- p sl assert ram_read_check (ram_re,  (addrb = raddr10), (raddr10 >= "10100000000"), (raddr10 <= "10110101001"));
-- p sl assert ram_read_check (ram_re,  (addra = raddr11), (raddr11 >= "11000000000"), (raddr11 <= "11010111010"));

-- Verify that the proper level RAM address is selected
-- and the RAM address is within the acceptable range during a write
-- and post incremented write address is still in acceptable range
-- pl property ram_waddr1_check is always {push(0) = '1'} |->
-- {(addra = waddr1 AND addra >= "00000000000" AND addra <= "0000010000") ; push(0) = '0' AND
-- waddr1 >= "00000000000" AND waddr1 <= "0000010000" };
-- pl assert ram_waddr1_check;

-- pl property ram_waddr2_check is always {push(1) = '1'} |-> 
-- {(addra = waddr2 AND addra >= "00001000000" AND addra <= "00001100001"); push(1) = '0' AND
-- waddr2 >= "00001000000" AND waddr2 <= "00001100001" };
-- pl assert ram_waddr2_check;

-- pl property ram_waddr3_check is always {push(2) = '1'} |-> 
-- {(addra = waddr3 AND addra >= "00010000000" AND addra <= "00010110010"); push(2) = '0' AND
-- waddr3 >= "00010000000" AND waddr3 <= "00010110010" };
-- pl assert ram_waddr3_check;

-- pl property ram_waddr4_check is always {push(3) = '1'} |-> 
-- {(addra = waddr4 AND addra >= "00100000000" AND addra <= "00101000011"); push(3) = '0' AND
-- waddr4 >= "00100000000" AND waddr4 <= "00101000011" };
-- pl assert ram_waddr4_check;

-- pl property ram_waddr5_check is always {push(4) = '1'} |-> 
-- {(addra = waddr5 AND addra >= "00110000000" AND addra <= "00111010100"); push(4) = '0' AND
-- waddr5 >= "00110000000" AND waddr5 <= "00111010100" };
-- pl assert ram_waddr5_check;

-- pl property ram_waddr6_check is always {push(5) = '1'} |-> 
-- {(addra = waddr6 AND addra >= "01000000000" AND addra <= "01001100101"); push(5) = '0' AND
-- waddr6 >= "01000000000" AND waddr6 <= "01001100101" };
-- pl assert ram_waddr6_check;

-- pl property ram_waddr7_check is always {push(6) = '1'} |-> 
-- {(addra = waddr7 AND addra >= "01010000000" AND addra <= "01011110110"); push(6) = '0' AND
-- waddr7 >= "01010000000" AND waddr7 <= "01011110110" };
-- pl assert ram_waddr7_check;

-- pl property ram_waddr8_check is always {push(7) = '1'} |-> 
-- {(addra = waddr8 AND addra >= "01100000000" AND addra <= "01110000111"); push(7) = '0' AND
-- waddr8 >= "01100000000" AND waddr8 <= "01110000111" };
-- pl assert ram_waddr8_check;

-- pl property ram_waddr9_check is always {push(8) = '1'} |-> 
-- {(addra = waddr9 AND addra >= "10000000000" AND addra <= "10010011000"); push(8) = '0' AND
-- waddr9 >= "10000000000" AND waddr9 <= "10010011000" };
-- pl assert ram_waddr9_check;

-- pl property ram_waddr10_check is always {push(9) = '1'} |-> 
-- {(addra = waddr10 AND addra >= "10100000000" AND addra <= "10110101001"); push(9) = '0' AND
-- waddr10 >= "10100000000" AND waddr10 >= "10100000000" };
-- pl assert ram_waddr10_check;

-- pl property ram_waddr11_check is always {push(10) = '1'} |-> 
-- {(addra = waddr11 AND addra >= "11000000000" AND addra <= "11010111010"); push(10) = '0' AND
--  waddr11 >= "11000000000" AND waddr11 <= "11010111010" };
-- pl assert ram_waddr11_check;


-- Verify that the proper level RAM address is selected
-- and the RAM address is within the acceptable range during a read
-- pl property ram_raddr1_check is always {(ram_re = '1' AND addrb = raddr1)} |->
-- {addrb >= "00000000000" AND addrb <= "0000010000" ; ram_re = '0'};
-- pl assert ram_raddr1_check;

-- pl property ram_raddr2_check is always {(ram_re = '1' AND addrb = raddr2)} |->
-- {addrb >= "00001000000" AND addrb <= "00001100001"; ram_re = '0'};
-- pl assert ram_raddr2_check;

-- pl property ram_raddr3_check is always {(ram_re = '1' AND addrb = raddr3)} |->
-- {addrb >= "00010000000" AND addrb <= "00010110010"; ram_re = '0'};
-- pl assert ram_raddr3_check;

-- pl property ram_raddr4_check is always {(ram_re = '1' AND addrb = raddr4)} |->
-- {addrb >= "00100000000" AND addrb <= "00101000011"; ram_re = '0'};
-- pl assert ram_raddr4_check;

-- pl property ram_raddr5_check is always {(ram_re = '1' AND addrb = raddr5)} |->
-- {addrb >= "00110000000" AND addrb <= "00111010100"; ram_re = '0'};
-- pl assert ram_raddr5_check;

-- pl property ram_raddr6_check is always {(ram_re = '1' AND addrb = raddr6)} |->
-- {addrb >= "01000000000" AND addrb <= "01001100101"; ram_re = '0'};
-- pl assert ram_raddr6_check;

-- pl property ram_raddr7_check is always {(ram_re = '1' AND addrb = raddr7)} |->
-- {addrb >= "01010000000" AND addrb <= "01011110110"; ram_re = '0'};
-- pl assert ram_raddr7_check;

-- pl property ram_raddr8_check is always {(ram_re = '1' AND addrb = raddr8)} |->
-- {addrb >= "01100000000" AND addrb <= "01110000111"; ram_re = '0'};
-- pl assert ram_raddr8_check;

-- pl property ram_raddr9_check is always {(ram_re = '1' AND addrb = raddr9)} |->
-- {addrb >= "10000000000" AND addrb <= "10010011000"; ram_re = '0'};
-- pl assert ram_raddr9_check;

-- pl property ram_raddr10_check is always {(ram_re = '1' AND addrb = raddr10)} |->
-- {addrb >= "10100000000" AND addrb <= "10110101001"; ram_re = '0'};
-- pl assert ram_raddr10_check;

-- pl property ram_raddr11_check is always {(ram_re = '1' AND addrb = raddr11)} |->
-- {addrb >= "11000000000" AND addrb <= "11010111010"; ram_re = '0'};
-- pl assert ram_raddr11_check;


begin

  ram_we <= '1' when push /= "00000000000" else '0';  
  add_p1 <= ten_zeros & '1';

-- write address mux
  with sel select
   addra <= waddr1  when "0000",
            waddr2  when "0001",
            waddr3  when "0010",
            waddr4  when "0011",
            waddr5  when "0100",
            waddr6  when "0101",
            waddr7  when "0110",
            waddr8  when "0111",
            waddr9  when "1000",
            waddr10 when "1001",
            waddr11 when others;

-- read address mux
  with sel select
   addrb <= raddr1  when "0000",
            raddr2  when "0001",
            raddr3  when "0010",
            raddr4  when "0011",
            raddr5  when "0100",
            raddr6  when "0101",
            raddr7  when "0110",
            raddr8  when "0111",
            raddr9  when "1000",
            raddr10 when "1001",
            raddr11 when others;

-- increment the write address pointers if they are selected
-- and there is a write to the ram. Check for max address
-- before incrementing. If max address is reached then reset
-- address to initial value. The rising_edge clock and reset
-- are not prioritized per Pat Harkin's coding suggestion tip
  process(clk,reset_n)
  begin
    if(rising_edge(clk)) then
      if(push /= "00000000000") then
        case sel is
          when "0000" =>
            if(waddr1 = "0000010000") then -- 16
              waddr1 <= (others => '0');   -- 0
            else
              waddr1  <= waddr1  + add_p1;
            end if;
          when "0001" =>
            if(waddr2 = "00001100001") then -- 97
              waddr2 <= "00001000000";      -- 64
            else
               waddr2  <= waddr2  + add_p1;
            end if;
          when "0010" =>
            if(waddr3 = "00010110010") then -- 178
              waddr3 <= "00010000000";      -- 128
            else
              waddr3  <= waddr3  + add_p1;
            end if;
          when "0011" =>
            if(waddr4 = "00101000011") then -- 323
              waddr4 <= "00100000000";      -- 256
            else
              waddr4  <= waddr4  + add_p1;
            end if;
          when "0100" =>
            if(waddr5 = "00111010100") then -- 468
              waddr5 <= "00110000000";      -- 384
            else
              waddr5  <= waddr5  + add_p1;
            end if;
          when "0101" =>
            if(waddr6 = "01001100101") then -- 613
              waddr6 <= "01000000000";      -- 512
            else
              waddr6  <= waddr6  + add_p1;
            end if;
          when "0110" =>
            if(waddr7 = "01011110110") then -- 758
              waddr7 <= "01010000000";      -- 640
            else
              waddr7  <= waddr7  + add_p1;
            end if;
          when "0111" =>
            if(waddr8 = "01110000111") then -- 903
              waddr8 <= "01100000000";      -- 768
            else
              waddr8  <= waddr8  + add_p1;
            end if;
          when "1000" =>
            if(waddr9 = "10010011000") then -- 1176
              waddr9 <= "10000000000";      -- 1024
            else
              waddr9  <= waddr9  + add_p1;
            end if;
          when "1001" =>
            if(waddr10 = "10110101001") then -- 1449
              waddr10 <= "10100000000";      -- 1280
            else
              waddr10 <= waddr10 + add_p1;
            end if;
          when others =>
            if (BUG = 0) then
              if(waddr11 = "11010111010") then -- 1722
                waddr11 <= "11000000000";      -- 1536
              else
                waddr11 <= waddr11 + add_p1;
              end if;
            else
              if(waddr11 = "11010111100") then -- 1724
                waddr11 <= "11000000000";      -- 1536
              else
                waddr11 <= waddr11 + add_p1;
              end if;
            end if;
        end case;
      end if;
    end if;
    if(reset_n = '0') then
      waddr1  <= "00000000000";-- 0
      waddr2  <= "00001000000";-- 64
      waddr3  <= "00010000000";-- 128
      waddr4  <= "00100000000";-- 256
      waddr5  <= "00110000000";-- 384
      waddr6  <= "01000000000";-- 512
      waddr7  <= "01010000000";-- 640
      waddr8  <= "01100000000";-- 768
      waddr9  <= "10000000000";-- 1024
      waddr10 <= "10100000000";-- 1280
      waddr11 <= "11000000000";-- 1536
    end if;
  end process;


-- the read address pointers needs to increment each
-- time the write pointers are incremented. The ram read
-- are initialized to the write address plus 1. Check for
-- the max address before incrementing. If max address is
-- reached then reset address to initial value. The
-- rising_edge clock and reset are not prioritized per
-- Pat Harkin's coding suggestion tip
  process(clk,reset_n)
  begin
    if(rising_edge(clk)) then
      if(push /= "00000000000") then
        case sel is
          when "0000" =>
            if(raddr1 = "0000010000") then -- 16
              raddr1 <= (others => '0');   -- 0
            else
              raddr1  <= raddr1  + add_p1;
            end if;
          when "0001" =>
            if(raddr2 = "00001100001") then -- 97
              raddr2 <= "00001000000";      -- 64
            else
               raddr2  <= raddr2  + add_p1;
            end if;
          when "0010" =>
            if(raddr3 = "00010110010") then -- 178
              raddr3 <= "00010000000";      -- 128
            else
              raddr3  <= raddr3  + add_p1;
            end if;
          when "0011" =>
            if(raddr4 = "00101000011") then -- 323
              raddr4 <= "00100000000";      -- 256
            else
              raddr4  <= raddr4  + add_p1;
            end if;
          when "0100" =>
            if(raddr5 = "00111010100") then -- 468
              raddr5 <= "00110000000";      -- 384
            else
              raddr5  <= raddr5  + add_p1;
            end if;
          when "0101" =>
            if(raddr6 = "01001100101") then -- 613
              raddr6 <= "01000000000";      -- 512
            else
              raddr6  <= raddr6  + add_p1;
            end if;
          when "0110" =>
            if(raddr7 = "01011110110") then -- 758
              raddr7 <= "01010000000";      -- 640
            else
              raddr7  <= raddr7  + add_p1;
            end if;
          when "0111" =>
            if(raddr8 = "01110000111") then -- 903
              raddr8 <= "01100000000";      -- 768
            else
              raddr8  <= raddr8  + add_p1;
            end if;
          when "1000" =>
            if(raddr9 = "10010011000") then -- 1176
              raddr9 <= "10000000000";      -- 1024
            else
              raddr9  <= raddr9  + add_p1;
            end if;
          when "1001" =>
            if(raddr10 = "10110101001") then -- 1449
              raddr10 <= "10100000000";      -- 1280
            else
              raddr10 <= raddr10 + add_p1;
            end if;
          when others =>
            if(raddr11 = "11010111010") then -- 1722
              raddr11 <= "11000000000";      -- 1536
            else
              raddr11 <= raddr11 + add_p1;
            end if;
        end case;
      end if;
    end if;
    if(reset_n = '0') then
      raddr1  <= "00000000000";-- 0
      raddr2  <= "00001000000";-- 64
      raddr3  <= "00010000000";-- 128
      raddr4  <= "00100000000";-- 256
      raddr5  <= "00110000000";-- 384
      raddr6  <= "01000000000";-- 512
      raddr7  <= "01010000000";-- 640
      raddr8  <= "01100000000";-- 768
      raddr9  <= "10000000000";-- 1024
      raddr10 <= "10100000000";-- 1280
      raddr11 <= "11000000000";-- 1536
    end if;
  end process;

ram_block : entity work.ram2p_2kx8
  port map (
    wclk   => clk,
    din    => din,
    waddr  => addra,
    we     => ram_we,
    re     => ram_re,
    rclk   => clk,
    raddr  => addrb,
    dout   => dout
   );

--ram_block : ram2048x8
--  generic map (
--      PORTA_MAX_ADDR_SIZE => PORTA_MAX_ADDR_SIZE
--    )
--    clk             => clk,
--    reset_n         => reset_n,
--    scan_enable     => scan_enable,
--    din             => din,
--    waddr           => addra,
--    raddr           => addrb,
--    push            => push,
--    re              => ram_re,
--    dout            => dout
--   );

end RTL;
