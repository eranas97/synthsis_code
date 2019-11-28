library IEEE;
use IEEE.STD_LOGIC_1164.all;
USE IEEE.STD_LOGIC_ARITH.all;
USE IEEE.STD_LOGIC_UNSIGNED.all;

entity POST_PROCESSOR is
  port (CLOCK: in STD_LOGIC;
        RESET: in STD_LOGIC;
        POINTER: in STD_LOGIC_VECTOR(13 downto 0);
        FS_DATA: in STD_LOGIC_VECTOR(7 downto 0);
        FS_ADDR: out STD_LOGIC_VECTOR(18 downto 0);
        FS_READ: out STD_LOGIC;
        FS_MUX: out STD_LOGIC;
        COMMON_RST: in STD_LOGIC;
        RXD: out STD_LOGIC;
        DISABLE_SCRAM: in STD_LOGIC;
        IN_SYNC: out STD_LOGIC;
        TEST_MODE: in STD_LOGIC;
        BUFFER_SHIFT_IN: out STD_LOGIC;
        BUFFER_DATA_OUT: out STD_LOGIC; 
        TXC: in STD_LOGIC;
        STROBE_128K: out STD_LOGIC);
end;

architecture RTL of POST_PROCESSOR is
signal RCOUNTA: STD_LOGIC_VECTOR(4 downto 0);
signal CNTA_BORROW: STD_LOGIC;
signal RCOUNTB: STD_LOGIC_VECTOR(4 downto 0);
signal CNTB_BORROW: STD_LOGIC;
signal RCOUNTC: STD_LOGIC_VECTOR(3 downto 0);
signal COUNTA : STD_LOGIC_VECTOR(4 downto 0);
signal COUNTB : STD_LOGIC_VECTOR(4 downto 0);
signal CNTA_CARRY: STD_LOGIC;
signal COLUMN_COUNT : STD_LOGIC_VECTOR(9 downto 0);
signal LOADCHAN0: STD_LOGIC;
signal LOADCHAN1: STD_LOGIC;
signal PRELOAD: STD_LOGIC;
signal DECREMENT: STD_LOGIC;
signal BITS: STD_LOGIC_VECTOR(15 downto 0) ;
signal SERIAL_INC: STD_LOGIC;
signal SERIAL_FALLEDGE: STD_LOGIC;
signal COUNT: STD_LOGIC_VECTOR(3 downto 0);
signal LOADCHAN0P: STD_LOGIC;
signal LOADCHAN1P: STD_LOGIC;
signal ERROR_COUNT: STD_LOGIC_VECTOR(2 downto 0);
signal SYNC_FLAG: STD_LOGIC;  -- This did have an initial value.
signal SYNC_ERROR: STD_LOGIC; -- This did have an initial value.
signal SWAP: STD_LOGIC;
signal LSB_ADD: STD_LOGIC;
signal RETIME_COUNT: STD_LOGIC;
signal MODEBITS: STD_LOGIC_VECTOR(15 downto 0) ;
signal BIT_STROBE: STD_LOGIC;
signal OVERHEAD0: STD_LOGIC;
signal OVERHEAD1: STD_LOGIC;
signal BIT_STA: STD_LOGIC;
signal BIT_STB: STD_LOGIC;

begin

-- ROW COUNTER
-- The row counter is a 14 bit counter
-- tracking the 16K lines of data.
RCOUNTER: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      RCOUNTA <= "00000";
    elsif PRELOAD = '1' then
      RCOUNTA <= POINTER(4 downto 0);
    elsif DECREMENT = '1' then
      RCOUNTA <= RCOUNTA - '1';
    end if;
    if RESET = '0' then
      RCOUNTB <= "00000";
    elsif PRELOAD = '1' then
      RCOUNTB <= POINTER(9 downto 5);
    elsif DECREMENT = '1' and CNTA_BORROW = '1' then
      RCOUNTB <= RCOUNTB - '1';
    end if;
    if RESET = '0' then
      RCOUNTC <= "0000";
    elsif PRELOAD = '1' then
      RCOUNTC <= POINTER(13 downto 10);
    elsif DECREMENT = '1' and CNTB_BORROW = '1' then
      RCOUNTC <= RCOUNTC - '1';
    end if;
end process;
-- Produces the strobes necessary for the row
-- counter.
RSTROBES: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      CNTA_BORROW <= '0';
    elsif RCOUNTA = "00000" or
       (POINTER(4 downto 0) = "00000" and PRELOAD = '1') then
      CNTA_BORROW <= '1';
    else
      CNTA_BORROW <= '0';
    end if;
    if RESET = '0' then 
      CNTB_BORROW <= '0' ;
    elsif (RCOUNTA = "00000" and RCOUNTB = "00000") or
          (POINTER(9 downto 0) = "0000000000" and PRELOAD = '1') then
      CNTB_BORROW <= '1' ;
    else
      CNTB_BORROW <= '0' ;
    end if;
end process;
-- COLUMN COUNTER
-- The column counter is a 5 bit counter
-- tracking the 32 columns
CCOUNTER: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if COMMON_RST = '0' or RESET = '0' then
      COUNTA <= "00000";
    else
      COUNTA <= COUNTA + '1';
    end if;
    if COUNTA = "11110" then
      CNTA_CARRY <= '1';
    else
      CNTA_CARRY <= '0';
    end if;
    if COMMON_RST = '0' or RESET = '0' then 
      COUNTB <= "00000"; 
    elsif CNTA_CARRY = '1' then 
      COUNTB <= COUNTB + '1'; 
    end if;
end process;
-- STROBE GENERATOR
-- The strobe generator produces the strobes
-- necessary to control the post processor.
STROBES: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      LOADCHAN0 <= '0';
    elsif COLUMN_COUNT = "0001000100" then
      LOADCHAN0 <= '1';
    else
      LOADCHAN0 <= '0';
    end if;
    if RESET = '0' then 
      LOADCHAN1 <= '0';
    elsif COLUMN_COUNT = "0010000100" then
      LOADCHAN1 <= '1';
    else
      LOADCHAN1 <= '0';
    end if;
    if RESET = '0' then
      SERIAL_INC <= '0';
    elsif COLUMN_COUNT(5 downto 0) = "000101" then
      SERIAL_INC <= '1';
    else
      SERIAL_INC <= '0';
    end if;
    if RESET = '0' then
      SERIAL_FALLEDGE <= '0';
    elsif COLUMN_COUNT(5 downto 0) = "100101" then
      SERIAL_FALLEDGE <= '1';
    else
      SERIAL_FALLEDGE <= '0';
    end if;
    if RESET = '0' then
      FS_MUX <= '0';
    elsif COLUMN_COUNT(9 downto 2) = "00010001" or
       COLUMN_COUNT(9 downto 2) = "00100001" then
      FS_MUX <= '1';
    else
      FS_MUX <= '0';
    end if;
    if RESET = '0' then
      PRELOAD <= '0';
      DECREMENT <= '0';
    elsif SWAP = '1' then
      if COLUMN_COUNT = "0000001111" or COLUMN_COUNT = "0001001111" then
        PRELOAD <= '1';
      else
        PRELOAD <= '0';
      end if;
      if COLUMN_COUNT = "0000010101" then
        DECREMENT <= '1';
      else
        DECREMENT <= '0';
      end if;
    else
      if COLUMN_COUNT = "0000001111" then
        PRELOAD <= '1';
      else
        PRELOAD <= '0';
      end if;
      if COLUMN_COUNT = "0001000101" then
        DECREMENT <= '1';
      else
        DECREMENT <= '0';
      end if;
    end if;
    if RESET = '0' then
      BIT_STROBE <= '0';
    elsif ((COLUMN_COUNT(9 downto 4) = "001011" or
            COLUMN_COUNT(9 downto 4) = "001100") and
            COLUMN_COUNT(1 downto 0) = "10") or
          ((COLUMN_COUNT(9 downto 4) = "001001" or 
            COLUMN_COUNT(9 downto 4) = "001010") and 
            COLUMN_COUNT(1 downto 0) = "10") then
      BIT_STROBE <= '1';
    else
      BIT_STROBE <= '0';
    end if;
    if RESET = '0' then
      OVERHEAD0 <= '1';
    elsif LOADCHAN0P = '1' then
      if RCOUNTB(0) = '0' and RCOUNTA = "00000" then
        OVERHEAD0 <= '0';
      else
        OVERHEAD0 <= '1';
      end if;
    end if;
    if RESET = '0' then
      BIT_STA <= '0';
    elsif ((COLUMN_COUNT(9 downto 4) = "001001" or
            COLUMN_COUNT(9 downto 4) = "001010") and
            COLUMN_COUNT(1 downto 0) = "00") and OVERHEAD0 = '1' then
      BIT_STA <= '1';
    else
      BIT_STA <= '0';
    end if;
    if RESET = '0' then
      BIT_STB <= '0';
    elsif ((COLUMN_COUNT(9 downto 4) = "001011" or
            COLUMN_COUNT(9 downto 4) = "001100") and
            COLUMN_COUNT(1 downto 0) = "00") and OVERHEAD1 = '1' then
      BIT_STB <= '1';
    else
      BIT_STB <= '0';
    end if;
    if RESET = '0' then
      OVERHEAD1 <= '1';
    elsif LOADCHAN1P = '1' then
      if RCOUNTB(0) = '0' and RCOUNTA = "00000" then
        OVERHEAD1 <= '0';
      else
        OVERHEAD1 <= '1';
      end if;
    end if;
    if RESET = '0' then
      BUFFER_SHIFT_IN <= '0';
    else
      BUFFER_SHIFT_IN <= BIT_STA or BIT_STB;
    end if;
end process;
-- SERIAL STORE MULTIPLEXER
-- Points to the latest bit to be transmitted
-- out of the serial interface.
SERIAL_MUX: process (BITS,COUNT)
begin
  case COUNT is
    when "0000" =>
      RXD <= BITS(0);
    when "0001" =>
      RXD <= BITS(1);
    when "0010" =>
      RXD <= BITS(2);
    when "0011" =>
      RXD <= BITS(3);
    when "0100" =>
      RXD <= BITS(4);
    when "0101" =>
      RXD <= BITS(5);
    when "0110" =>
      RXD <= BITS(6);
    when "0111" =>
      RXD <= BITS(7);
    when "1000" =>
      RXD <= BITS(8);
    when "1001" =>
      RXD <= BITS(9);
    when "1010" =>
      RXD <= BITS(10);
    when "1011" =>
      RXD <= BITS(11);
    when "1100" =>
      RXD <= BITS(12);
    when "1101" =>
      RXD <= BITS(13);
    when "1110" =>
      RXD <= BITS(14);
    when "1111" =>
      RXD <= BITS(15);
    when others =>
      RXD <= BITS(0);
  end case;
end process;
-- SERIAL STORE AND SYNC DETECTION
-- Contains the storage of the latest two
-- bytes to be transmitted along with the
-- serial counter which is used as a pointer
-- to the bit being output.
SERIAL_REG: process
  begin
    wait until RISING_EDGE (CLOCK) ;
      -- Shift Register Storage
      if RESET = '0' then
        BITS(7 downto 0) <= "00000000";
      elsif LOADCHAN0P = '1' then
        BITS(7 downto 0) <= FS_DATA;
      end if;
      if RESET = '0' then
        BITS(15 downto 8) <= "00000000";
      elsif LOADCHAN1P = '1' then
        BITS(15 downto 8) <= FS_DATA;
      end if;
      if RESET = '0' then
        LOADCHAN0P <= '0';
        LOADCHAN1P <= '0';
      else
        -- Retime load strobes
        LOADCHAN0P <= LOADCHAN0 ;
        LOADCHAN1P <= LOADCHAN1 ;
      end if;
      -- Serial Data Output Counter 
      if COMMON_RST = '0' or RESET = '0' then
        COUNT <= "1110";
      elsif SERIAL_INC = '1' then
        COUNT <= COUNT + '1';
      end if;
end process;
-- Monitors incoming data to synchronise on the
-- alternating mark/space data.
SYNC_DETECT: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      SYNC_FLAG <= '0';
      ERROR_COUNT <= "000";
    elsif DISABLE_SCRAM = '0' then
          SYNC_FLAG <= '1';
          ERROR_COUNT <= "000";
    elsif COMMON_RST = '0' then
      if SYNC_ERROR = '1' then
        if ERROR_COUNT = "111" then
          SYNC_FLAG <= not(SYNC_FLAG);
          ERROR_COUNT <= "111";
        else
          SYNC_FLAG <= BITS(0);
          ERROR_COUNT <= "000";
        end if;
      else
        SYNC_FLAG <= not(SYNC_FLAG);
        if ERROR_COUNT = "111" then
          ERROR_COUNT <= "111";
        else
          ERROR_COUNT <= ERROR_COUNT + '1';
        end if;
      end if;
    end if;
    if RESET = '0' then
      SYNC_ERROR <= '1';  
    elsif SYNC_FLAG = not(BITS(0)) then
      SYNC_ERROR <= '0';
    else
      SYNC_ERROR <= '1';
    end if;
end process;

-- Modifies the value of fs_addr in
-- test mode only.
MODIFY_ADDR: process(RCOUNTA,RCOUNTC,TEST_MODE,COLUMN_COUNT(9 downto 6),LSB_ADD)
begin
if TEST_MODE = '0' then
  FS_ADDR <= RCOUNTC & RCOUNTB & RCOUNTA & COLUMN_COUNT(9 downto 6) & LSB_ADD ;
else
  FS_ADDR <= RCOUNTC & RCOUNTB & RCOUNTA & COLUMN_COUNT(9 downto 6) & LSB_ADD
  and "1111110000111111111";
end if;
end process;

-- MODE TWO SUPPORT
MODE_TWO: process
  begin
    wait until RISING_EDGE (CLOCK) ;
      if RESET = '0' then
        MODEBITS <= "0000000000000000";
      elsif LOADCHAN0P = '1' then
        MODEBITS(7 downto 0) <= FS_DATA;
      elsif LOADCHAN1P = '1' then
        MODEBITS(15 downto 8) <= FS_DATA;
      elsif BIT_STROBE = '1' then
      for A in 0 to 14 loop
        MODEBITS(A) <= MODEBITS(A + 1);
      end loop;
      end if;
end process;

-- Signal Assignments (internal).
SWAP <= not(SYNC_FLAG);
COLUMN_COUNT <= COUNTB & COUNTA;
LSB_ADD <= not(SWAP xor COLUMN_COUNT(6));

-- Signal Assignments (external).
FS_READ <= not(LOADCHAN1 or LOADCHAN0);
IN_SYNC <= ERROR_COUNT(2) and ERROR_COUNT(1) and ERROR_COUNT(0);
BUFFER_DATA_OUT <= MODEBITS(0);
STROBE_128K <= SERIAL_INC or SERIAL_FALLEDGE;

end RTL;
