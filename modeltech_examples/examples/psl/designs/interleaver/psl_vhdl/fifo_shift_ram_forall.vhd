library ieee;
    use ieee.std_logic_1164.all;
    use ieee.std_logic_unsigned.all;
    use ieee.std_logic_arith.all;
library work;
    use work.all;

entity fifo_shift_ram is
  generic (
     PORTA_MAX_ADDR_SIZE        : NATURAL  :=11;
     BUG                        : INTEGER  :=0
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

  type range_array is array (1 to 11) of integer;
  type addr_array is array (11 downto 1) of std_logic_vector(10 downto 0);

  constant ten_zeros : std_logic_vector(9 downto 0) := (others => '0');
  constant hirange : range_array := (16,97,178,323,468,613,758,903,1176,1449,1722);
  constant lorange : range_array := ( 0,64,128,256,384,512,640,768,1024,1280,1536);


  signal addr    : std_logic_vector(10 downto 0);
  signal addra   : std_logic_vector(10 downto 0);
  signal addrb   : std_logic_vector(10 downto 0);
  signal waddr   : addr_array;
  signal raddr   : addr_array;
  signal add_p1  : std_logic_vector(10 downto 0);
  signal ram_we  : std_logic;


-- Default assertion clock
-- psl default clock is rising_edge(clk);

-- Verify that only one level of the RAM is written at a time
-- psl property push_mutex_check is always {ram_we} |-> { onehot(push); NOT(ram_we)};
-- psl assert push_mutex_check;

-- Verify that the proper level RAM address is selected
-- and the RAM address is within the acceptable range during a write
-- and post incremented write address is still in acceptable range
-- psl property ram_write_check is forall i in {1 to 11} : always
-- {push(i-1) = '1'} |-> {addra = waddr(i) AND waddr(i) >= conv_std_logic_vector(lorange(i),11) AND
-- waddr(i) <= conv_std_logic_vector(hirange(i),11); push(i-1) = '0' AND
-- waddr(i) >= conv_std_logic_vector(lorange(i),11) AND waddr(i) <= conv_std_logic_vector(hirange(i),11)};

-- psl assert ram_write_check;


-- Verify that the proper level RAM address is selected
-- and the RAM address is within the acceptable range during a read
-- psl property ram_read_check is forall i in {1 to 11} : always
-- {ram_re = '1' AND addrb = raddr(i)} |-> {raddr(i) >= conv_std_logic_vector(lorange(i),11) AND
-- raddr(i) <= hirange(i); ram_re = '0'};

-- psl assert ram_read_check;

begin

  ram_we <= '1' when push /= "00000000000" else '0';  
  add_p1 <= ten_zeros & '1';

-- write address mux
  with sel select
   addra <= waddr(1)  when "0000",
            waddr(2)  when "0001",
            waddr(3)  when "0010",
            waddr(4)  when "0011",
            waddr(5)  when "0100",
            waddr(6)  when "0101",
            waddr(7)  when "0110",
            waddr(8)  when "0111",
            waddr(9)  when "1000",
            waddr(10) when "1001",
            waddr(11) when others;

-- read address mux
  with sel select
   addrb <= raddr(1)  when "0000",
            raddr(2)  when "0001",
            raddr(3)  when "0010",
            raddr(4)  when "0011",
            raddr(5)  when "0100",
            raddr(6)  when "0101",
            raddr(7)  when "0110",
            raddr(8)  when "0111",
            raddr(9)  when "1000",
            raddr(10) when "1001",
            raddr(11) when others;

-- increment the write address pointers if they are selected
-- and there is a write to the ram. Check for max address
-- before incrementing. If max address is reached then reset
-- address to initial value.
  process(clk,reset_n)
  begin
    if(rising_edge(clk)) then
      if(push /= "00000000000") then
        case sel is
          when "0000" =>
            if(waddr(1) = "0000010000") then -- 16
              waddr(1) <= (others => '0');   -- 0
            else
              waddr(1)  <= waddr(1)  + add_p1;
            end if;
          when "0001" =>
            if(waddr(2) = "00001100001") then -- 97
              waddr(2) <= "00001000000";      -- 64
            else
               waddr(2)  <= waddr(2)  + add_p1;
            end if;
          when "0010" =>
            if(waddr(3) = "00010110010") then -- 178
              waddr(3) <= "00010000000";      -- 128
            else
              waddr(3)  <= waddr(3)  + add_p1;
            end if;
          when "0011" =>
            if(waddr(4) = "00101000011") then -- 323
              waddr(4) <= "00100000000";      -- 256
            else
              waddr(4)  <= waddr(4)  + add_p1;
            end if;
          when "0100" =>
            if(waddr(5) = "00111010100") then -- 468
              waddr(5) <= "00110000000";      -- 384
            else
              waddr(5)  <= waddr(5)  + add_p1;
            end if;
          when "0101" =>
            if(waddr(6) = "01001100101") then -- 613
              waddr(6) <= "01000000000";      -- 512
            else
              waddr(6)  <= waddr(6)  + add_p1;
            end if;
          when "0110" =>
            if(waddr(7) = "01011110110") then -- 758
              waddr(7) <= "01010000000";      -- 640
            else
              waddr(7)  <= waddr(7)  + add_p1;
            end if;
          when "0111" =>
            if(waddr(8) = "01110000111") then -- 903
              waddr(8) <= "01100000000";      -- 768
            else
              waddr(8)  <= waddr(8)  + add_p1;
            end if;
          when "1000" =>
            if(waddr(9) = "10010011000") then -- 1176
              waddr(9) <= "10000000000";      -- 1024
            else
              waddr(9)  <= waddr(9)  + add_p1;
            end if;
          when "1001" =>
            if(waddr(10) = "10110101001") then -- 1449
              waddr(10) <= "10100000000";      -- 1280
            else
              waddr(10) <= waddr(10) + add_p1;
            end if;
          when others =>
            if (BUG = 0) then
              if(waddr(11) = "11010111010") then -- 1722
                waddr(11) <= "11000000000";      -- 1536
              else
                waddr(11) <= waddr(11) + add_p1;
              end if;
            else
              if(waddr(11) = "11010111100") then -- 1724
                waddr(11) <= "11000000000";      -- 1536
              else
                waddr(11) <= waddr(11) + add_p1;
              end if;
            end if;
        end case;
      end if;
    end if;
    if(reset_n = '0') then
      waddr(1)  <= "00000000000";-- 0
      waddr(2)  <= "00001000000";-- 64
      waddr(3)  <= "00010000000";-- 128
      waddr(4)  <= "00100000000";-- 256
      waddr(5)  <= "00110000000";-- 384
      waddr(6)  <= "01000000000";-- 512
      waddr(7)  <= "01010000000";-- 640
      waddr(8)  <= "01100000000";-- 768
      waddr(9)  <= "10000000000";-- 1024
      waddr(10) <= "10100000000";-- 1280
      waddr(11) <= "11000000000";-- 1536
    end if;
  end process;


-- the read address pointers needs to increment each
-- time the write pointers are incremented. The ram read
-- are initialized to the write address plus 1. Check for
-- the max address before incrementing. If max address is
-- reached then reset address to initial value.
  process(clk,reset_n)
  begin
    if(rising_edge(clk)) then
      if(push /= "00000000000") then
        case sel is
          when "0000" =>
            if(raddr(1) = "0000010000") then -- 16
              raddr(1) <= (others => '0');   -- 0
            else
              raddr(1)  <= raddr(1)  + add_p1;
            end if;
          when "0001" =>
            if(raddr(2) = "00001100001") then -- 97
              raddr(2) <= "00001000000";      -- 64
            else
               raddr(2)  <= raddr(2)  + add_p1;
            end if;
          when "0010" =>
            if(raddr(3) = "00010110010") then -- 178
              raddr(3) <= "00010000000";      -- 128
            else
              raddr(3)  <= raddr(3)  + add_p1;
            end if;
          when "0011" =>
            if(raddr(4) = "00101000011") then -- 323
              raddr(4) <= "00100000000";      -- 256
            else
              raddr(4)  <= raddr(4)  + add_p1;
            end if;
          when "0100" =>
            if(raddr(5) = "00111010100") then -- 468
              raddr(5) <= "00110000000";      -- 384
            else
              raddr(5)  <= raddr(5)  + add_p1;
            end if;
          when "0101" =>
            if(raddr(6) = "01001100101") then -- 613
              raddr(6) <= "01000000000";      -- 512
            else
              raddr(6)  <= raddr(6)  + add_p1;
            end if;
          when "0110" =>
            if(raddr(7) = "01011110110") then -- 758
              raddr(7) <= "01010000000";      -- 640
            else
              raddr(7)  <= raddr(7)  + add_p1;
            end if;
          when "0111" =>
            if(raddr(8) = "01110000111") then -- 903
              raddr(8) <= "01100000000";      -- 768
            else
              raddr(8)  <= raddr(8)  + add_p1;
            end if;
          when "1000" =>
            if(raddr(9) = "10010011000") then -- 1176
              raddr(9) <= "10000000000";      -- 1024
            else
              raddr(9)  <= raddr(9)  + add_p1;
            end if;
          when "1001" =>
            if(raddr(10) = "10110101001") then -- 1449
              raddr(10) <= "10100000000";      -- 1280
            else
              raddr(10) <= raddr(10) + add_p1;
            end if;
          when others =>
            if(raddr(11) = "11010111010") then -- 1722
              raddr(11) <= "11000000000";      -- 1536
            else
              raddr(11) <= raddr(11) + add_p1;
            end if;
        end case;
      end if;
    end if;
    if(reset_n = '0') then
      raddr(1)  <= "00000000000";-- 0
      raddr(2)  <= "00001000000";-- 64
      raddr(3)  <= "00010000000";-- 128
      raddr(4)  <= "00100000000";-- 256
      raddr(5)  <= "00110000000";-- 384
      raddr(6)  <= "01000000000";-- 512
      raddr(7)  <= "01010000000";-- 640
      raddr(8)  <= "01100000000";-- 768
      raddr(9)  <= "10000000000";-- 1024
      raddr(10) <= "10100000000";-- 1280
      raddr(11) <= "11000000000";-- 1536
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
