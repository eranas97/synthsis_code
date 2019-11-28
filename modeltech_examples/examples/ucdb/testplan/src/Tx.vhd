library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;

entity TX_PROCESS is
  port (RESET: in STD_LOGIC;
        CLOCK: in STD_LOGIC;
        CRC_WRITE: out STD_LOGIC;
        CRC_READ: out STD_LOGIC;
        VARIABLE_ADDRESS: out STD_LOGIC_VECTOR(4 downto 0);
        STATE_CONTROL: in STD_LOGIC_VECTOR(1 downto 0);
        MODE_CONTROL: in STD_LOGIC_VECTOR(1 downto 0);
        CHAN_ADD_BIT: in STD_LOGIC;
        TEST_MODE: in STD_LOGIC;
        CHANENB: in STD_LOGIC_VECTOR(4 downto 0);
        FIFO_RAM_DATA: in STD_LOGIC_VECTOR(7 downto 0);
        FIFO_FULL_INDICATE: in STD_LOGIC;
        FIFO_OUT_CLOCK: out STD_LOGIC;
        MICRO_INTERRUPT: out STD_LOGIC;
        CRC_IN: in STD_LOGIC_VECTOR(3 downto 0);
        CRC_OUT: out STD_LOGIC_VECTOR(3 downto 0);
        CRC_ENABLE: in STD_LOGIC;
        TXD: in STD_LOGIC;
        TXC: out STD_LOGIC;
        IOM_SDS1: in STD_LOGIC;
        IOM_SDS2: in STD_LOGIC;
        PRES1M: out STD_LOGIC;
        PRES8M: out STD_LOGIC;
        SWAP_CHAN: in STD_LOGIC;
        SWAP_BYTE: in STD_LOGIC;
        TX_PATTERN: in STD_LOGIC;
        IOM_DCK: in STD_LOGIC;
        IOM_DU: out STD_LOGIC;
        OPEN_COLLECTOR: out STD_LOGIC;
        NOT_CRC_READ: out STD_LOGIC;
        RESET_FIFO: in STD_LOGIC;
        FIFO_RESET: out STD_LOGIC;
        INT_ACK: in STD_LOGIC;
        DATA_STROBE: out STD_LOGIC;
        SLOT_WINDOW: out STD_LOGIC;
        OVERHEAD_OCTET: out STD_LOGIC;
        BUFFER_IN: in STD_LOGIC);

end;

architecture RTL of TX_PROCESS is

type STATESIX is (C1,C2,C3,C4,C5,C6);
constant IDLE: STD_LOGIC_VECTOR (1 downto 0) := "00";
constant MC_NEGOTIATE: STD_LOGIC_VECTOR (1 downto 0) := "01";
constant WIDEBAND_BUILD: STD_LOGIC_VECTOR (1 downto 0) := "10";
constant DATA: STD_LOGIC_VECTOR (1 downto 0) := "11";
constant ZERO: STD_LOGIC_VECTOR (1 downto 0) := "00";
constant ONE: STD_LOGIC_VECTOR (1 downto 0) := "01";
constant TWO: STD_LOGIC_VECTOR (1 downto 0) := "10";
constant THREE: STD_LOGIC_VECTOR (1 downto 0) := "11";
signal OCTET_TYPE : STD_LOGIC_VECTOR(2 downto 0);
signal SOUT : STD_LOGIC_VECTOR(4 downto 0);
signal SFULL : STD_LOGIC;
signal RETIME_CRC_RISE: STD_LOGIC;
signal RETIME_CRC_FALL: STD_LOGIC;
signal CRC_STB: STD_LOGIC;
signal P4_STROBE: STD_LOGIC;
signal P4_STROBE_B: STD_LOGIC;
signal CRC_READ_B: STD_LOGIC;
signal BIT_STROBE_B: STD_LOGIC;
signal BIT_STROBE: STD_LOGIC;
signal OCT_COUNT: STD_LOGIC_VECTOR(4 downto 0);
signal COLUMN_STROBE: STD_LOGIC;
signal CRC_READ_STROBE: STD_LOGIC;
signal COUT : STD_LOGIC_VECTOR(4 downto 0);
signal STROBE_128K_B: STD_LOGIC;
signal STROBE_128K: STD_LOGIC;
signal ROW_STROBE: STD_LOGIC;
signal COLUMN_COUNT: STD_LOGIC_VECTOR(4 downto 0);
signal ROUT: STD_LOGIC_VECTOR(7 downto 0);
signal FULLCOUNT_B: STD_LOGIC;
signal FEED_FRAME: STD_LOGIC;
signal HALF_STROBE: STD_LOGIC;
signal ROW_COUNT: STD_LOGIC_VECTOR(7 downto 0);
signal FOUT : STD_LOGIC_VECTOR(5 downto 0);
signal DOUBLE_STROBE: STD_LOGIC;
signal FRAME_COUNT: STD_LOGIC_VECTOR(5 downto 0);
type BONDING_FSM is (SIDLE,MCNEG,BUILD,NO_OVERHEAD,ADD2,
            M2DATA,ADD3,M3DATA);
signal FSM_STATE: BONDING_FSM ;
type OCTETS is (CLAMP,ICHAN,FAW,FCNT,CRC,ODATA);
signal CONTROL_OUT: OCTETS ;
signal IC_OCTET_B: STD_LOGIC;
signal CRC_OCTET_B: STD_LOGIC;
signal IC_OCTET: STD_LOGIC;
signal CRC_OCTET: STD_LOGIC;
signal TX_DATA: STD_LOGIC;
signal CRC_DOUT: STD_LOGIC;
signal SERIAL_FC: STD_LOGIC;
signal INFO_CHAN_DOUT: STD_LOGIC;
signal SERIAL_FAW: STD_LOGIC;
signal OVERHEAD: STD_LOGIC;
signal INFOCHAN: STD_LOGIC_VECTOR(7 downto 0);
signal A_BIT: STD_LOGIC;
signal E_BIT: STD_LOGIC;
signal LOAD_IC: STD_LOGIC;
signal LOAD_AE: STD_LOGIC;
signal FIFO_READY: STD_LOGIC;
signal UNLOCK_FIFO: STD_LOGIC;
signal MASK_INT: STD_LOGIC;
signal INT0: STD_LOGIC;
signal INT1: STD_LOGIC;
signal INT: STD_LOGIC;
signal INT2: STD_LOGIC;
signal CRC_DATA: STD_LOGIC_VECTOR(3 downto 0);
signal CLEAR_CRC: STD_LOGIC;
signal DCOUNT: STATESIX ;
signal DFULL: STD_LOGIC ;
signal FSC_RESET: STD_LOGIC ;
signal FSCPLUSONE: STD_LOGIC ;
signal LCOUNT: STD_LOGIC_VECTOR(4 downto 0);
signal GCIBITS: STD_LOGIC_VECTOR(15 downto 0) ;
signal SWAPPER: STD_LOGIC; -- Had inital vale of '0'
signal IOMCOUNT: STD_LOGIC_VECTOR(3 downto 0);
signal IOMPOINTER: STD_LOGIC_VECTOR(3 downto 0) ;
signal IOM_ENABLE: STD_LOGIC;
signal IOM_RESET: STD_LOGIC;
signal IOM_RETIME_ONE: STD_LOGIC;
signal IOM_RETIME_TWO: STD_LOGIC;
signal COM_RETIME_ONE: STD_LOGIC;
signal COM_RETIME_TWO: STD_LOGIC;
signal JITTER: STD_LOGIC;
signal JITTER_PULSE: STD_LOGIC;
signal DATA_OUT: STD_LOGIC;
signal SELECTOR: STD_LOGIC_VECTOR(1 downto 0);
signal PRESCALE: STD_LOGIC;
signal COMMON_BUS_DATA_IN: STD_LOGIC;
signal SERIALBITS: STD_LOGIC_VECTOR(15 downto 0) ;
signal COLUMN_SLOTS: STD_LOGIC_VECTOR(3 downto 0) ;
signal COMMON_BUS_RESET: STD_LOGIC;
signal SLOT_STROBE: STD_LOGIC;
signal SERIAL_IN: STD_LOGIC;
signal INT_TXD: STD_LOGIC;
signal COLUMN_MATCH : BOOLEAN;

-- PSL default clock is rising_edge(CLOCK);

-- PSL sequence FSM_IDLE_TO_NEG is
--     {FSM_STATE = SIDLE; FSM_STATE = MCNEG };
-- PSL Cover_FSM_IDLE_TO_NEG : cover FSM_IDLE_TO_NEG ;
-- PSL sequence FSM_IDLE_TO_BUILD is
--     {FSM_STATE = SIDLE; FSM_STATE = BUILD};
-- PSL Cover_FSM_IDLE_TO_BUILD : cover FSM_IDLE_TO_BUILD ;
-- PSL sequence FSM_IDLE_TO_M2DATA is
--     {FSM_STATE = SIDLE; FSM_STATE = M2DATA};
-- PSL Cover_FSM_IDLE_TO_M2DATA : cover FSM_IDLE_TO_M2DATA ;
-- PSL sequence FSM_IDLE_TO_M3DATA is
--     {FSM_STATE = SIDLE; FSM_STATE = M3DATA};
-- PSL Cover_FSM_IDLE_TO_M3DATA : cover FSM_IDLE_TO_M3DATA ;
-- PSL sequence FSM_ADD_CHANNEL_MODE3 is
--     {FSM_STATE = M3DATA; FSM_STATE = ADD3};
-- PSL Cover_FSM_ADD_CHANNEL_MODE3 : cover FSM_ADD_CHANNEL_MODE3 ;
-- PSL sequence FSM_ADD_CHANNEL_MODE2 is
--     {FSM_STATE = M2DATA; FSM_STATE = ADD2};
-- PSL Cover_FSM_ADD_CHANNEL_MODE2 : cover FSM_ADD_CHANNEL_MODE2 ;

begin
-- STROBE COUNTER
-- 5 Bit Strobe Counter
SCOUNT: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if COMMON_BUS_RESET = '0' or RESET = '0' then
      SOUT <= "00000";
    else
      SOUT <= SOUT + '1';
    end if;
end process;
-- Strobe Decoder And Generator
STROBES: process(SOUT)
begin
  case SOUT is
  when "00000" =>
    CRC_READ_B <= '0' ;
    SFULL <= '0' ;
    BIT_STROBE_B <= '1' ;
    CRC_STB <= '0' ;
    P4_STROBE_B <= '0' ;
  when "00100" | "01000" | "01100" | "10000" |
       "10100" | "11000" | "11100" =>
    CRC_READ_B <= '1' ;
    SFULL <= '0' ;
    BIT_STROBE_B <= '1' ;
    CRC_STB <= '0' ;
    P4_STROBE_B <= '0' ;
  when "00001" | "00101" | "01001" | "01101" | "10001" |
       "10101" | "11001" | "11101" =>
    CRC_READ_B <= '1' ;
    BIT_STROBE_B <= '0' ;
    SFULL <= '0' ;
    CRC_STB <= '0' ;
    P4_STROBE_B <= '0' ;
  WHEN "00010" | "00110" | "01010" | "01110" |
       "10010" | "10110" | "11010"  =>
    CRC_READ_B <= '1' ;
    SFULL <= '0' ;
    BIT_STROBE_B <= '0' ;
    CRC_STB <= '0' ;
    P4_STROBE_B <= '1' ;
  when "11111" =>
    CRC_READ_B <= '1' ;
    SFULL <= '0' ;
    BIT_STROBE_B <= '0' ;
    CRC_STB <= '1' ;
    P4_STROBE_B <= '0' ;
  when "11110" =>
    CRC_READ_B <= '1' ;
    SFULL <= '1' ;
    BIT_STROBE_B <= '0' ;
    CRC_STB <= '0' ;
    P4_STROBE_B <= '1' ;
  when others =>
    CRC_READ_B <= '1' ;
    SFULL <= '0' ;
    BIT_STROBE_B <= '0' ;
    CRC_STB <= '0' ;
    P4_STROBE_B <= '0' ;
  end case ;
end process;
-- Retime the Strobes that are generated by the
-- Strobe Decoder on the rising edge of the CLOCK,
-- Also retimes other signals from other Strobe Decoders.
RETIME_STROBES_RISE: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      RETIME_CRC_RISE <= '0';
      CRC_READ_STROBE <= '1';
      P4_STROBE <= '0';
      COLUMN_STROBE <= '0';
      BIT_STROBE <= '0';
      STROBE_128K <= '0';
      FEED_FRAME <= '0';
      IC_OCTET <= '0' ; 
      CRC_OCTET <= '0' ;
    else
      RETIME_CRC_RISE <= CRC_STB ;
      CRC_READ_STROBE <= CRC_READ_B ;
      P4_STROBE <= P4_STROBE_B ;
      COLUMN_STROBE <= SFULL ;
      BIT_STROBE <= BIT_STROBE_B ;
      STROBE_128K <= STROBE_128K_B ;
      FEED_FRAME <= FULLCOUNT_B ;
      IC_OCTET <= IC_OCTET_B ; 
      CRC_OCTET <= CRC_OCTET_B ;
    end if;
end process;
-- Retime the Strobes that are generated by the 
-- Strobe Decoder on the falling edge of the CLOCK.
RETIME_STROBES_RISE_FALL: process
begin
  wait until FALLING_EDGE (CLOCK) ;
    if RESET = '0' then
      RETIME_CRC_FALL <= '0';
    else
      RETIME_CRC_FALL <= CRC_STB ;
    end if;
end process;
-- COLUMN COUNTER
-- 5 bit Column Counter
CCOUNT: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if COMMON_BUS_RESET = '0' or RESET = '0' then
      COUT <= "00000";
    elsif COLUMN_STROBE = '1' then
      COUT <= COUT + '1';
    end if;
end process;
-- Strobe Decoder And Generator
COLUMN_STROBES: process(COUT,COLUMN_STROBE)
begin
  if COLUMN_STROBE = '1' then
    case COUT is
    when "11111" =>
      ROW_STROBE <= '1' ;
      STROBE_128K_B <= '0';
    when "00000" | "00010" | "00100" | "00110" | "01000" | "01010" |
         "01100" | "01110" | "10000" | "10010" | "10100" | "10110" |
         "11000" | "11010" | "11100" | "11110" =>
      ROW_STROBE <= '0' ;
      STROBE_128K_B <= '1';
    when others =>
      ROW_STROBE <= '0' ;
      STROBE_128K_B <= '0';
    end case;
  else
    ROW_STROBE <= '0' ;
    STROBE_128K_B <= '0';
  end if;
end process;
-- ROW COUNTER
-- 8 bit Row Counter
RCOUNT: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      ROUT <= "00000000";
    elsif ROW_STROBE = '1' then
      ROUT <= ROUT + '1';
    end if;
end process;
-- Strobe Decoder And Generator
ROW_STROBES: process(ROUT,ROW_STROBE)
begin
  if ROW_STROBE = '1' then
    case ROUT is
    when "00111111" =>
      HALF_STROBE <= '0' ;
      FULLCOUNT_B <= '0' ;
    when "01111111" =>
      HALF_STROBE <= '1' ;
      FULLCOUNT_B <= '0' ;
    when "10111111" =>
      HALF_STROBE <= '0' ;
      FULLCOUNT_B <= '0' ;
    when "11111111" =>
      HALF_STROBE <= '1' ;
      FULLCOUNT_B <= '1' ;
    when others =>
      HALF_STROBE <= '0' ;
      FULLCOUNT_B <= '0' ;
    end case;
  else
    HALF_STROBE <= '0' ;
    FULLCOUNT_B <= '0' ;
  end if ;
end process;
-- FRAME COUNTER
-- 6 bit Frame Counter
FCOUNT: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      FOUT <= "000000";
    elsif FEED_FRAME = '1' then
      FOUT <= FOUT + '1';
    end if;
end process;
-- Strobe Decoder And Generator
FRAME_STROBES: process(FOUT,FEED_FRAME)
begin
  if FEED_FRAME = '1' then
    case FOUT is
    when "000001" |  "000011" |  "000101" |  "000111" |
         "001001" |  "001011" |  "001101" |  "001111" |
         "010001" |  "010011" |  "010101" |  "010111" |
         "011001" |  "011011" |  "011101" |  "011111" |
         "100001" |  "100011" |  "100101" |  "100111" |
         "101001" |  "101011" |  "101101" |  "101111" |
         "110001" |  "110011" |  "110101" |  "110111" |
         "111001" |  "111011" |  "111101" |  "111111" =>
      DOUBLE_STROBE <= '1' ;
    when others =>
      DOUBLE_STROBE <= '0' ;
    end case ;
  else
    DOUBLE_STROBE <= '0' ;
  end if;
end process;
-- STATE MACHINE
-- The transmit state machine is controled by the BONDING
-- mode and the state. The first part of the machine is
-- to decode these values to select which part of the state
-- machine to function in.
STATE_SELECT: process
begin
  wait until RISING_EDGE (CLOCK);
  if RESET = '0' then
    FSM_STATE <= SIDLE ;
  else
    case STATE_CONTROL is
    when IDLE =>
      FSM_STATE <= SIDLE ;
    when MC_NEGOTIATE =>
      FSM_STATE <= MCNEG ;
    when WIDEBAND_BUILD =>
      FSM_STATE <= BUILD ;
    when DATA =>
        case MODE_CONTROL is
        when ZERO =>
          FSM_STATE <= NO_OVERHEAD ;
        when ONE =>
          FSM_STATE <= NO_OVERHEAD ;
        when TWO =>
          if CHAN_ADD_BIT = '1' then
            FSM_STATE <= ADD2 ;
          else
            FSM_STATE <= M2DATA;
          end if;
        when THREE =>
          if CHAN_ADD_BIT = '1' then
            FSM_STATE <= ADD3 ;
          else
            FSM_STATE <= M3DATA;
          end if;
        when others =>
          null;
        end case;
    when others =>
      null;
    end case;
  end if;
end process;
-- The state machine holds the function of each of the
-- states that are possible.
OCTET_TYPE <= ROW_COUNT(7 downto 5) when TEST_MODE = '0' else ROW_COUNT(3 downto 1);
COLUMN_MATCH <= (COLUMN_COUNT = ROW_COUNT(4 downto 0)) when TEST_MODE = '0' else (COLUMN_COUNT(0) = ROW_COUNT(0));
STATE_MACHINE: process
begin
  wait until RISING_EDGE (CLOCK);
  if RESET = '0' then
    CONTROL_OUT <= CLAMP ;
  else
    case FSM_STATE is
    when SIDLE =>
      CONTROL_OUT <= CLAMP ;
    when MCNEG =>
      if COLUMN_COUNT < CHANENB then
        CONTROL_OUT <= ICHAN ;
      else
        CONTROL_OUT <= CLAMP ;
      end if ;
    when BUILD =>
      if COLUMN_COUNT < CHANENB then
        if COLUMN_MATCH then
          case OCTET_TYPE is
          when "000" =>
            CONTROL_OUT <= FAW;
          when "010" =>
            CONTROL_OUT <= ICHAN;
          when "100" =>
            CONTROL_OUT <= FCNT;
          when "110" =>
            CONTROL_OUT <= CRC;
          when others =>
            CONTROL_OUT <= CLAMP;
          end case;
        else
          CONTROL_OUT <= CLAMP;
        end if;
      else
        CONTROL_OUT <= CLAMP;
      end if ;
    when NO_OVERHEAD =>
      if COLUMN_COUNT < CHANENB then
        CONTROL_OUT <= ODATA ;
      else
        CONTROL_OUT <= CLAMP ;
      end if ;
    when M2DATA =>
      if COLUMN_COUNT < CHANENB then
        if COLUMN_MATCH then
          case OCTET_TYPE is
          when "000" =>
            CONTROL_OUT <= FAW;
          when "010" =>
            CONTROL_OUT <= ICHAN;
          when "100" =>
            CONTROL_OUT <= FCNT;
          when "110" =>
            CONTROL_OUT <= CRC;
          when others =>
            CONTROL_OUT <= ODATA;
          end case;
        else
          CONTROL_OUT <= ODATA;
        end if;
      else
        CONTROL_OUT <= CLAMP;
      end if ;
    when M3DATA =>
      CONTROL_OUT <= CLAMP;
    when ADD2 =>
      CONTROL_OUT <= ODATA;
    when ADD3 =>
      CONTROL_OUT <= ODATA;
    when others =>
      null ;
    end case ;
  end if ;
end process ;
-- Used to set the overhead signal to show if the current
-- octet is BONDING overhead.
OVERHEAD_INSERTED: process(CONTROL_OUT)
begin
  case CONTROL_OUT is
  when CLAMP | ODATA =>
    OVERHEAD <= '0';
  when others =>
    OVERHEAD <= '1';
  end case;
end process ;
-- Used to indicate whether the current position is a 
-- CRC or IC octet.
CRC_AE_POSITION: process(COLUMN_COUNT,ROW_COUNT,FSM_STATE)
begin
case FSM_STATE is
  when MCNEG =>
  if COLUMN_COUNT = 0 then
    IC_OCTET_B <= '1';
    CRC_OCTET_B <= '0';
  else
    IC_OCTET_B <= '0';
    CRC_OCTET_B <= '0';
  end if;
  when others =>
  if COLUMN_MATCH then
    case OCTET_TYPE is
    when "010" =>
      IC_OCTET_B <= '1';
      CRC_OCTET_B <= '0';
    when "110" =>
      IC_OCTET_B <= '0';
      CRC_OCTET_B <= '1';
    when others =>
      IC_OCTET_B <= '0';
      CRC_OCTET_B <= '0';
    end case;
  else
    IC_OCTET_B <= '0';
    CRC_OCTET_B <= '0';
  end if;
  end case ;
end process ;
-- CONTROL DATA MUX
-- The control mux is the data multiplexer that selects the
-- current data path dependant on the type of octet to be
-- transmitted.
CTRL_MUX: process
begin
  wait until RISING_EDGE(CLOCK);
    if RESET = '0' then 
        TX_DATA <= '0';
    else
      case CONTROL_OUT is
        when FAW =>
          TX_DATA <= SERIAL_FAW;
        when ICHAN =>
          TX_DATA <= INFO_CHAN_DOUT;
        when FCNT =>
          TX_DATA <= SERIAL_FC;
        when CRC =>
          TX_DATA <= CRC_DOUT;
        when ODATA =>
          TX_DATA <= SERIAL_IN;
        when CLAMP =>
          TX_DATA <= '1';
      end case;
    end if;
end process;
-- FRAME COUNT MUx
-- The Frame Count Mux selects each of the bits of the 
-- current frame count for transmitting in order.
FRAME_COUNT_MUX: process (OCT_COUNT,FRAME_COUNT)
  begin
    case OCT_COUNT (4 downto 2) is
      when "000" =>
        SERIAL_FC <= '1';
      when "001" =>
        SERIAL_FC <= FRAME_COUNT(5);
      when "010" =>
        SERIAL_FC <= FRAME_COUNT(4);
      when "011" =>
        SERIAL_FC <= FRAME_COUNT(3);
      when "100" =>
        SERIAL_FC <= FRAME_COUNT(2);
      when "101" =>
        SERIAL_FC <= FRAME_COUNT(1);
      when "110" =>
        SERIAL_FC <= FRAME_COUNT(0);
      when "111" =>
        SERIAL_FC <= '1';
      when others =>
        NULL;
    end case;
end process;
-- FAW GENERATOR
-- Generates the FAW word.
FAW_MUX: process (OCT_COUNT)
begin
  case OCT_COUNT (4 downto 2) is
    when "000" =>
      SERIAL_FAW <= '0';
    when "001" =>
      SERIAL_FAW <= '0';
    when "010" =>
      SERIAL_FAW <= '0';
    when "011" =>
      SERIAL_FAW <= '1';
    when "100" =>
      SERIAL_FAW <= '1';
    when "101" =>
      SERIAL_FAW <= '0';
    when "110" =>
      SERIAL_FAW <= '1';
    when "111" =>
      SERIAL_FAW <= '1';
    when others =>
      NULL;
    end case;
end process;
-- INFORMATION CHANNEL
-- Holds the latest IC byte from the FIFO
IC_STORAGE: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' or UNLOCK_FIFO = '0' then
      INFOCHAN <= "11111111";
    elsif (LOAD_IC = '1' and UNLOCK_FIFO = '1') then
      INFOCHAN <= FIFO_RAM_DATA;
    end if;
end process;
-- Produces a serial bit stream of the latest IC byte.
IC_OUTPUT_MUX: process (OCT_COUNT(4 downto 2),INFOCHAN)
begin
  case OCT_COUNT (4 downto 2) is
    when "000" =>
      INFO_CHAN_DOUT <= INFOCHAN(0);
    when "001" =>
      INFO_CHAN_DOUT <= INFOCHAN(1);
    when "010" =>
      INFO_CHAN_DOUT <= INFOCHAN(2);
    when "011" =>
      INFO_CHAN_DOUT <= INFOCHAN(3);
    when "100" =>
      INFO_CHAN_DOUT <= INFOCHAN(4);
    when "101" =>
      INFO_CHAN_DOUT <= INFOCHAN(5);
    when "110" =>
      INFO_CHAN_DOUT <= INFOCHAN(6);
    when "111" =>
      INFO_CHAN_DOUT <= INFOCHAN(7);
    when others =>
        NULL;
  end case;
end process;
IM_FUNC:process
begin
  wait until RISING_EDGE (CLOCK) ;
-- A & E bits stored
    if RESET = '0' then
      A_BIT <= '0' ;
      E_BIT <= '0' ;
    elsif (LOAD_AE = '1' and UNLOCK_FIFO = '1') then
      A_BIT <= FIFO_RAM_DATA (0) ;
      E_BIT <= FIFO_RAM_DATA (1) ;
    end if;
-- Re-times the Full indication from the FIFO.
    if RESET = '0' then
      FIFO_READY <= '0';
    elsif RESET_FIFO = '1' then
      FIFO_READY <= '0';
    elsif FIFO_FULL_INDICATE = '0' then
      FIFO_READY <= '1';
    end if ;
-- Unlocks the FIFO on the next row strobe
    if RESET = '0' then
      UNLOCK_FIFO <= '0';
    elsif RESET_FIFO = '1' then
      UNLOCK_FIFO <= '0';
    elsif FIFO_READY = '1' then
        case STATE_CONTROL is
        when IDLE =>
            UNLOCK_FIFO <= '0';
        when others =>
          if FEED_FRAME = '1' then
            UNLOCK_FIFO <= '1';
          end if ;
        end case ;
    end if ;
-- Masks the first interrupt once the FIFO is unlocked
    if RESET = '0' then
      MASK_INT <= '0' ;
    elsif RESET_FIFO = '1' then
      MASK_INT <= '0' ;
    elsif (BIT_STROBE = '1' and UNLOCK_FIFO = '1') then
      MASK_INT <= '1' ;
    end if;
end process;
-- Generates the strobes to load the IC and A & E bits
GENERATE_LOADS:process(STATE_CONTROL,CRC_READ_STROBE,UNLOCK_FIFO,IC_OCTET,CRC_OCTET)
begin
  LOAD_AE <= '0' ;
  case STATE_CONTROL is
  when IDLE =>
    LOAD_AE <= '0' ;
    LOAD_IC <= '0' ;
  when MC_NEGOTIATE =>
    if (CRC_READ_STROBE = '0' and UNLOCK_FIFO = '1' and IC_OCTET = '1') then
      LOAD_IC <= '1' ;
    else
      LOAD_IC <= '0' ;
    end if ;
  when others =>
    if (CRC_READ_STROBE = '0' and UNLOCK_FIFO = '1' and IC_OCTET = '1') then
      LOAD_IC <= '1' ;
    else
      LOAD_IC <= '0' ;
    end if ;
    if (CRC_READ_STROBE = '0' and UNLOCK_FIFO = '1' and CRC_OCTET = '1') then
      LOAD_AE <= '1' ;
    else
      LOAD_AE <= '0' ;
    end if ;
  end case ;
end process;
-- produces interrupt in normal frames
GENERATE_INT0:process(MASK_INT,STATE_CONTROL,DOUBLE_STROBE)
begin
  if MASK_INT = '1' then
    case STATE_CONTROL is
    when IDLE | MC_NEGOTIATE =>
      INT0 <= '0' ;
    when others =>
      if DOUBLE_STROBE = '1' then
        INT0 <= '1' ;
      else
        INT0 <= '0' ;
      end if;
    end case ;
  else
    INT0 <= '0' ;
  end if;
end process;
-- Produces interrupt in master channel frames
GENERATE_INT1:process(MASK_INT,STATE_CONTROL,HALF_STROBE)
begin
  if MASK_INT = '1' then
    case STATE_CONTROL is
    when MC_NEGOTIATE =>
      if HALF_STROBE = '1' then
        INT1 <= '1' ;
      else
        INT1 <= '0' ;
      end if;
    when others =>
      INT1 <= '0' ;
    end case ;
  else
    INT1 <= '0' ;
  end if;
end process;
-- Retimes the interrupt and fifo clock to stop glitches
LATCH_INT_CLK:process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      INT <= '0';
      FIFO_OUT_CLOCK <= '0' ;
    else
      INT <= INT0 or INT1 ;
      FIFO_OUT_CLOCK <= LOAD_IC or LOAD_AE;
    end if;
-- Allows interrupt to be cleared by the micro
    if INT_ACK ='1' or RESET = '0' then
      INT2 <= '0';
    else
      INT2 <= INT2 or INT;
    end if;
end process;
-- CRC GENERATOR
-- The CRC Generator produces a CRC4 of the last 255
-- octets transmitted.
CRC4: process
begin
 wait until RISING_EDGE (CLOCK);
  if RESET = '0' then
    CRC_DATA <= "0000";
  elsif CLEAR_CRC = '1' then
    CRC_DATA <= "0000";
  elsif CRC_ENABLE = '0' then
    CRC_DATA <= "1111";
  elsif CRC_READ_STROBE = '0' then
    CRC_DATA <= CRC_IN;
  elsif P4_STROBE = '1' and CRC_OCTET = '0' then
    CRC_DATA(3) <= TX_DATA xor CRC_DATA(0);
    CRC_DATA(2) <= CRC_DATA(3) xor (CRC_DATA(0) xor TX_DATA);
    CRC_DATA(1) <= CRC_DATA(2);
    CRC_DATA(0) <= CRC_DATA(1);
  else
    null;
  end if;
-- Added instead of OUTFF's in the PGA
-- version.
  if RESET = '0' then
    VARIABLE_ADDRESS <= "00000";
  else
    VARIABLE_ADDRESS <= COLUMN_COUNT ;
  end if;
end process;
-- Selects each of the bits of the CRC octet to be
-- transmitted.
CRC_MUX: process (OCT_COUNT(4 downto 2),A_BIT,E_BIT,CRC_DATA)
begin
  case OCT_COUNT (4 downto 2) is
    when "000" =>
      CRC_DOUT <= '1';
    when "001" =>
      CRC_DOUT <= A_BIT;
    when "010" =>
      CRC_DOUT <= E_BIT;
    when "011" =>
      CRC_DOUT <= CRC_DATA(0);
    when "100" =>
      CRC_DOUT <= CRC_DATA(1);
    when "101" =>
      CRC_DOUT <= CRC_DATA(2);
    when "110" =>
      CRC_DOUT <= CRC_DATA(3);
    when "111" =>
      CRC_DOUT <= '1';
    when others =>
      null;
   end case;
end process;
-- Clear the CRC store at the start of the calculation
CLR_CRC: process (OCT_COUNT, CRC_OCTET)
begin
  if CRC_OCTET = '1' and OCT_COUNT = "11100" then
    CLEAR_CRC <= '1';
  else
    CLEAR_CRC <= '0';
  end if;
end process;
-- DIVIDE BY SIX
-- Divides the 1.536MHz DCK by six to produce 256KHz
-- the input to the phase lock loop. The clock produced
-- is reset by an 8KHz signal from the GCI interface so
-- that its edges are kept away from the 8KHz signal. This
-- is because the Prescale output is phase and frequency 
-- locked to it and used to retime the 8KHz.
DIV6_STATE_MAC: process
begin
  wait until RISING_EDGE (IOM_DCK);
  if FSC_RESET = '0' or RESET = '0' then
    DCOUNT <= C3 ;
  else
    case DCOUNT is
    when C1 =>
      DCOUNT <= C2 ;
    when C2 =>
      DCOUNT <= C3 ;
    when C3 =>
      DCOUNT <= C4 ;
    when C4 =>
      DCOUNT <= C5 ;
    when C5 =>
      DCOUNT <= C6 ;
    when C6 =>
      DCOUNT <= C1 ;
    end case ;
  end if;
  if RESET = '0' then
    PRES1M <= '0';
  else
    PRES1M <= DFULL ;
    FSCPLUSONE <= not(IOM_SDS2);
  end if;
end process;
-- Produces the divide by six output.
DIV6_OUT: process(DCOUNT)
begin
  case DCOUNT is
  when C1 | C2 | C3 =>
    DFULL <= '0' ;
  when C4 | C5 | C6 =>
    DFULL <= '1' ;
  end case ;
end process;
-- PRESCALE COUNTER
-- Divides the 8.192MHz clock by 32 to produce 256KHz
-- the other input into the phase lock loop.
PCOUNTER: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      LCOUNT <= "00000";
    else
      LCOUNT <= LCOUNT + '1' ;
    end if;
end process;
-- IOM INTERFACE
-- Stores data to be transmitted on the GCI interface.
GCI_SHIFT_REG: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      GCIBITS <= "0000000000000000";
    elsif P4_STROBE = '1' and SLOT_STROBE = '1' then
      GCIBITS <= GCIBITS(14 downto 0) & TX_DATA;
    end if;
end process;
-- Adjusts the pointer to the IOM store so that the
-- Bytes can be swaped depending on the value of the
-- micro control bits.
POINTER_GEN: process(SELECTOR,SWAPPER,IOMCOUNT,SWAP_CHAN,SWAP_BYTE)
begin
  SELECTOR <= SWAP_CHAN & SWAP_BYTE;
  case SELECTOR is
  when "00" =>
    IOMPOINTER <= IOMCOUNT;
  when "10" =>
    IOMPOINTER(2 downto 0) <= IOMCOUNT(2 downto 0);
    IOMPOINTER(3)          <= not(IOMCOUNT(3));
  when "01" =>
    if SWAPPER = '0' then
      IOMPOINTER <= IOMCOUNT;
    else
      IOMPOINTER(2 downto 0) <= IOMCOUNT(2 downto 0);
      IOMPOINTER(3)          <= not(IOMCOUNT(3));
    end if;
  when "11" =>
    if SWAPPER = '1' then
      IOMPOINTER <= IOMCOUNT;
    else
      IOMPOINTER(2 downto 0) <= IOMCOUNT(2 downto 0);
      IOMPOINTER(3)          <= not(IOMCOUNT(3));
    end if;
  when others =>
    IOMPOINTER <= IOMCOUNT;
  end case;
end process;
-- Uses the iom pointer to select the bit for transmitting
-- and the data strobes to determined where to transmit the
-- bytes in the GCI frame.
DATA_ONTO_GCI: process(IOMPOINTER,GCIBITS,IOM_SDS1,IOM_SDS2)
begin
  if IOM_SDS1 = '1' or IOM_SDS2 = '1' then
  case IOMPOINTER is
  when "1111" =>
    DATA_OUT <= GCIBITS(0);
  when "1110" =>
    DATA_OUT <= GCIBITS(1);
  when "1101" =>
    DATA_OUT <= GCIBITS(2);
  when "1100" =>
    DATA_OUT <= GCIBITS(3);
  when "1011" =>
    DATA_OUT <= GCIBITS(4);
  when "1010" =>
    DATA_OUT <= GCIBITS(5);
  when "1001" =>
    DATA_OUT <= GCIBITS(6);
  when "1000" =>
    DATA_OUT <= GCIBITS(7);
  when "0111" =>
    DATA_OUT <= GCIBITS(8);
  when "0110" =>
    DATA_OUT <= GCIBITS(9);
  when "0101" =>
    DATA_OUT <= GCIBITS(10);
  when "0100" =>
    DATA_OUT <= GCIBITS(11);
  when "0011" =>
    DATA_OUT <= GCIBITS(12);
  when "0010" =>
    DATA_OUT <= GCIBITS(13);
  when "0001" =>
    DATA_OUT <= GCIBITS(14);
  when "0000" =>
    DATA_OUT <= GCIBITS(15);
  when others =>
    null;
  end case;
  else
    DATA_OUT <= '0';
  end if;
end process;
-- Produces the counter to allow the pointer to 
-- be generated. Produces the retimed signals
-- to generate the iom reset. Produces the BCK
-- enable strobe for use with DCK.
IOM_GENERATOR: process
begin
  wait until RISING_EDGE (IOM_DCK) ;
    if IOM_RESET = '1' or RESET = '0' then
      IOMCOUNT <= "0001" ;
    elsif IOM_ENABLE = '1' then
      IOMCOUNT <= IOMCOUNT + '1' ;
    end if ;
    if RESET = '0' then
      IOM_RETIME_ONE <= '0';
      IOM_RETIME_TWO <= '0';
    else
      IOM_RETIME_ONE <= IOM_SDS1 ;
      IOM_RETIME_TWO <= not(IOM_RETIME_ONE);
    end if;
    if IOM_RESET = '1' or RESET = '0' then
      IOM_ENABLE <= '0' ;
    else
      IOM_ENABLE <= not(IOM_ENABLE);
    end if ;
end process;
-- Produces the swap control and the common bus
-- reset. Retimes the 8KHz signal with the generated
-- 256KHz signal.
GENERATE_SWAP: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      SWAPPER <= '0';
    elsif COM_RETIME_ONE = '0' and COM_RETIME_TWO = '0' then
      SWAPPER <= not(SWAPPER);
    end if;
    if RESET = '0' then
      JITTER_PULSE <= '0';
    else
      JITTER_PULSE <= not(PRESCALE);
    end if;
    if RESET = '0' then 
      JITTER <= '0';
    elsif PRESCALE = '1' and JITTER_PULSE = '1' then
      JITTER <= IOM_SDS2;
    end if;
    if RESET = '0' then
      COM_RETIME_ONE <= '0';
      COM_RETIME_TWO <= '0';
    else
      COM_RETIME_ONE <= JITTER ;
      COM_RETIME_TWO <= not(COM_RETIME_ONE);
    end if;
end process;
-- Allows the GCI interface to output the alternating
-- frames of mark/space. 
DATA_PATH: process(DATA_OUT,TX_PATTERN,SWAPPER,IOM_SDS1,IOM_SDS2)
begin
if TX_PATTERN = '0' then
  IOM_DU <= DATA_OUT;
  OPEN_COLLECTOR <= not((IOM_SDS1 nor IOM_SDS2) or DATA_OUT);
else
  IOM_DU <= SWAPPER;
  OPEN_COLLECTOR <= not((IOM_SDS1 nor IOM_SDS2) or SWAPPER);
end if;
end process;
-- SERIAL INTERFACE
-- Stores data from the incoming TXD line.
SERIAL_STORE: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      INT_TXD <= '0';
    elsif OCT_COUNT = "01000" and COLUMN_COUNT(0) = '1' then
      INT_TXD <= TXD;
    end if;
    if RESET = '0' then
      SERIALBITS <= "0000000000000000";
    elsif STROBE_128K = '1' then
      case COLUMN_COUNT(4 downto 1) is
      when "0000" =>
        SERIALBITS(0) <= INT_TXD ;
      when "0001" =>
        SERIALBITS(1) <= INT_TXD ;
      when "0010" =>
        SERIALBITS(2) <= INT_TXD ;
      when "0011" =>
        SERIALBITS(3) <= INT_TXD ;
      when "0100" =>
        SERIALBITS(4) <= INT_TXD ;
      when "0101" =>
        SERIALBITS(5) <= INT_TXD ;
      when "0110" =>
        SERIALBITS(6) <= INT_TXD ;
      when "0111" =>
        SERIALBITS(7) <= INT_TXD ;
      when "1000" =>
        SERIALBITS(8) <= INT_TXD ;
      when "1001" =>
        SERIALBITS(9) <= INT_TXD ;
      when "1010" =>
        SERIALBITS(10) <= INT_TXD ;
      when "1011" =>
        SERIALBITS(11) <= INT_TXD ;
      when "1100" =>
        SERIALBITS(12) <= INT_TXD ;
      when "1101" =>
        SERIALBITS(13) <= INT_TXD ;
      when "1110" =>
        SERIALBITS(14) <= INT_TXD ;
      when "1111" =>
        SERIALBITS(15) <= INT_TXD ;
      when others =>
        null;
      end case;
    end if;
end process;
-- Selects the data to output onto the 
-- common bus.
SERIAL_MUX: process (SERIALBITS,COLUMN_SLOTS)
begin
  case COLUMN_SLOTS is
    when "0000" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(0);
    when "0001" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(1);
    when "0010" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(2);
    when "0011" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(3);
    when "0100" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(4);
    when "0101" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(5);
    when "0110" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(6);
    when "0111" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(7);
    when "1000" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(8);
    when "1001" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(9);
    when "1010" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(10);
    when "1011" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(11);
    when "1100" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(12);
    when "1101" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(13);
    when "1110" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(14);
    when "1111" =>
      COMMON_BUS_DATA_IN <= SERIALBITS(15);
    when others =>
      COMMON_BUS_DATA_IN <= SERIALBITS(0);
  end case;
end process;

-- Signal Assignments (internal)
OCT_COUNT        <= SOUT;
COLUMN_COUNT     <= COUT;
ROW_COUNT        <= ROUT;
FRAME_COUNT      <= FOUT;
FSC_RESET        <= IOM_SDS2 or FSCPLUSONE;
SLOT_STROBE      <= (not (COLUMN_COUNT(1))) and (not(COLUMN_COUNT(4))) and
                    (not(COLUMN_COUNT(3))) and (not(COLUMN_COUNT(2)));
IOM_RESET        <= IOM_RETIME_ONE and IOM_RETIME_TWO ;
COMMON_BUS_RESET <= COM_RETIME_ONE or COM_RETIME_TWO ;
PRESCALE         <= LCOUNT(4);
COLUMN_SLOTS     <= COLUMN_COUNT(0) & OCT_COUNT(4 downto 2);
SERIAL_IN        <= COMMON_BUS_DATA_IN when
                    (MODE_CONTROL = ZERO or MODE_CONTROL = ONE) else BUFFER_IN;

-- Signal Assignments (external)
CRC_WRITE <= RETIME_CRC_RISE nand RETIME_CRC_FALL;
CRC_READ <= CRC_READ_STROBE ;
CRC_OUT <= CRC_DATA;
MICRO_INTERRUPT <= INT2;
NOT_CRC_READ <= not (CRC_READ_STROBE);
FIFO_RESET <= not(RESET_FIFO);
TXC <= COLUMN_COUNT(0);
PRES8M <= PRESCALE;
DATA_STROBE <= BIT_STROBE;
OVERHEAD_OCTET <= OVERHEAD;
SLOT_WINDOW <= SLOT_STROBE;

end RTL;
