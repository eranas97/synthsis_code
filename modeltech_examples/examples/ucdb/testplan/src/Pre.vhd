library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;

entity PRE_PROCESSOR is
  port (RESET: in STD_LOGIC;
        CLOCK: in STD_LOGIC;
        VARIABLE_ADDRESS: out STD_LOGIC_VECTOR(7 downto 0);
        VARIABLE_WRITE: out STD_LOGIC;
        VARIABLE_READ: out STD_LOGIC;
        VARIABLE_SAVE: out STD_LOGIC_VECTOR(7 downto 0);
        VARIABLE_RESTORE: in STD_LOGIC_VECTOR(7 downto 0);
        VARIABLE_RESET: in STD_LOGIC;
        DATA_MODE: in STD_LOGIC;
        FS_WRITE: out STD_LOGIC;
        FSDATENB_STROBE: out STD_LOGIC;
        FRAME_STORE_DATA: out STD_LOGIC_VECTOR(7 downto 0);
        IOM_DCK: in STD_LOGIC;
        IOM_SDS1: in STD_LOGIC;
        IOM_SDS2: in STD_LOGIC;
        ADDRESS_POINTER: out STD_LOGIC_VECTOR(13 downto 0);
        FS_ADDRESS: out STD_LOGIC_VECTOR(18 downto 0);
        IOM_DD: in STD_LOGIC;
        PRE8M: in STD_LOGIC;
        MASTER_CID_SYNC: out STD_LOGIC;
        MASTER_FRAME_SYNC: out STD_LOGIC;
        COMMON_RESET: out STD_LOGIC;
        TEST_MODE: in STD_LOGIC;
        GROUP_ID: in STD_LOGIC_VECTOR(5 downto 0);
        GROUP_ID_ERROR: out STD_LOGIC);
end;

architecture RTL of PRE_PROCESSOR is
signal VCC: STD_LOGIC;
signal VCOUNTA : STD_LOGIC_VECTOR(4 downto 0);
signal VCOUNTB : STD_LOGIC_VECTOR(4 downto 0);
signal VCOUNT_FULL: STD_LOGIC;
signal VCOUNT: STD_LOGIC_VECTOR(9 downto 0);
signal VARIABLE_NUMBER: STD_LOGIC_VECTOR(2 downto 0);
signal VARIABLE_COLUMN: STD_LOGIC_VECTOR(4 downto 0);
signal DELAYED_COLUMN: STD_LOGIC_VECTOR(4 downto 0);
signal DCOLUMN: STD_LOGIC_VECTOR(4 downto 0);
signal OCTET_STROBE: STD_LOGIC;
signal BIT_STROBE: STD_LOGIC;
signal CRC_STROBE: STD_LOGIC;
signal UP_DATE_POINTER: STD_LOGIC;
signal VAR_RD0: STD_LOGIC;
signal VAR_RD1: STD_LOGIC;
signal VAR_RD2: STD_LOGIC;
signal VAR_RD3: STD_LOGIC;
signal VAR_RD4: STD_LOGIC;
signal VAR_RD5: STD_LOGIC;
signal VAR_RD6: STD_LOGIC;
signal VAR_RD7: STD_LOGIC;
signal FSWR_STROBE: STD_LOGIC;
signal FSDAT_STROBE: STD_LOGIC;
signal FSADDR_ENB: STD_LOGIC;
signal REGISTER_CONTENTS: STD_LOGIC_VECTOR(10 downto 0);
signal COMPARE_FAW: STD_LOGIC;
signal COMPARE_ICHAN: STD_LOGIC;
signal FAW_POSITION: STD_LOGIC;
signal IC_POSITION: STD_LOGIC;
signal IC_SYNC_POSITION: STD_LOGIC;
signal OCTET_COUNT: STD_LOGIC_VECTOR(7 downto 0);
signal ICHAN_COUNT: STD_LOGIC_VECTOR(3 downto 0);
type FRAME_MAC_STATES is (SEARCH,MATCH,FOUND,ERROR);
signal ICHAN_STATE: FRAME_MAC_STATES;
signal IN_IC_STATE: FRAME_MAC_STATES;
signal FAW_SYNC_FOUND: STD_LOGIC;
signal ICHAN_RESET: STD_LOGIC;
signal IC_SYNC_FOUND: STD_LOGIC;
type MAC_STATES is (OUT_OF_SYNC,SEEN_ONCE,SEEN_TWICE,IN_SYNC,MISSED_ONCE,MISSED_TWICE);
signal FAW_STATE: MAC_STATES;
signal IN_FAW_STATE: MAC_STATES;
signal OCTET_COUNT_RESET: STD_LOGIC;
signal OCOUNTA: STD_LOGIC_VECTOR(3 downto 0);
signal OFULL: STD_LOGIC;
signal OCOUNTB: STD_LOGIC_VECTOR(3 downto 0);
signal ICOUNT: STD_LOGIC_VECTOR(3 downto 0);
signal STATES_ICHAN: STD_LOGIC_VECTOR(1 downto 0);
signal STATES_CHAN_ID: STD_LOGIC_VECTOR(1 downto 0);
signal STATES_FAW:STD_LOGIC_VECTOR(2 downto 0);
signal STATES_FRAME: STD_LOGIC_VECTOR(1 downto 0);
signal STATES_CRC: STD_LOGIC_VECTOR(1 downto 0);
signal FRAMES: STD_LOGIC_VECTOR(5 downto 0);
signal CHANNEL_ID: STD_LOGIC_VECTOR(4 downto 0);
signal FRCOUNTA: STD_LOGIC_VECTOR(2 downto 0);
signal FRCOUNTB: STD_LOGIC_VECTOR(2 downto 0);
signal FRFULL: STD_LOGIC;
signal FRAME_STATE: FRAME_MAC_STATES;
signal IN_FRAME_STATE: FRAME_MAC_STATES;
signal FRAME_POSITION: STD_LOGIC;
signal FRAME_MATCHED: STD_LOGIC;
signal FRAME_SYNC_FOUND: STD_LOGIC;
signal STORE_FRAMES: STD_LOGIC_VECTOR(5 downto 0);
type PERSIST_MAC_STATES is (SEARCH,MATCH,FOUND_TWICE,FROZEN);
signal CHAN_ID_STATE: PERSIST_MAC_STATES;
signal CHAN_ID_SYNC: STD_LOGIC;
signal IN_CHAN_ID_STATE: PERSIST_MAC_STATES;
signal CHAN_ID_POSITION: STD_LOGIC;
signal CHAN_ID_MATCHED: STD_LOGIC;
signal CHANID_STORE: STD_LOGIC_VECTOR(4 downto 0);
signal CRC: STD_LOGIC_VECTOR(3 downto 0);
signal CRC_COMPARE: STD_LOGIC_VECTOR(3 downto 0);
signal CRC_RESET_STROBE: STD_LOGIC;
signal CRC_RESET: STD_LOGIC;
signal CRC_COMPARE_STROBE: STD_LOGIC;
signal CRC_STORE: STD_LOGIC_VECTOR(3 downto 0);
type CYC_STATE is (ENABLED,SEEN_ONCE,SEEN_TWICE,DISABLED);
signal CRCSTATE: CYC_STATE;
signal CRC_RESULT: STD_LOGIC;
signal IN_CRC_STATE: CYC_STATE;
signal CRC_ENABLED: STD_LOGIC;
signal CRC_POSITION: STD_LOGIC;
signal A: STD_LOGIC_VECTOR(13 downto 0);
signal B: STD_LOGIC_VECTOR(13 downto 0);
signal ADD13: STD_LOGIC;
signal CO00: STD_LOGIC;
signal CO02: STD_LOGIC;
signal CO01: STD_LOGIC;
signal CO03: STD_LOGIC;
signal CO04: STD_LOGIC;
signal CO05: STD_LOGIC;
signal CO06: STD_LOGIC;
signal CO07: STD_LOGIC;
signal CO08: STD_LOGIC;
signal CO09: STD_LOGIC;
signal CO10: STD_LOGIC;
signal CO11: STD_LOGIC;
signal CO12: STD_LOGIC;
signal STORE_FIRST_VALUE: STD_LOGIC;
signal ONE_SHOT: STD_LOGIC;
signal RETIME_ONE_SHOT: STD_LOGIC;
signal CALCULATED_VALUE: STD_LOGIC_VECTOR(13 downto 0);
signal STORED_VALUE: STD_LOGIC_VECTOR(13 downto 0);
signal MASTER_CHANNEL: STD_LOGIC;
signal IOM_ENABLE: STD_LOGIC;
signal IOM_RETIME_ONE: STD_LOGIC;
signal IOM_RETIME_TWO: STD_LOGIC;
signal IOM_RESET: STD_LOGIC;
signal IOMBITS: STD_LOGIC_VECTOR(15 downto 0);
signal RETIME_FCSA: STD_LOGIC;
signal RETIME_FCSB: STD_LOGIC;
signal JITTER_RESET: STD_LOGIC;
signal RETIME_PRE8M: STD_LOGIC;
signal JITTER_PULSE: STD_LOGIC;
signal DATA_IN: STD_LOGIC;
signal IOM_POINTER: STD_LOGIC_VECTOR(3 downto 0);
signal DATA_CLAMP: STD_LOGIC;
signal COMMON_RST: STD_LOGIC;
signal GROUP_ID_POSITION: STD_LOGIC;
signal GROUP_ID_MATCHED: STD_LOGIC;
signal GROUP_STORE: STD_LOGIC_VECTOR(5 downto 0);
signal GROUP_ID_STATE: PERSIST_MAC_STATES;
signal GROUP_ERROR: STD_LOGIC;
signal GROUP_ID_SYNC: STD_LOGIC;
signal IN_GROUP_ID_STATE: PERSIST_MAC_STATES;
signal STATES_GROUP: STD_LOGIC_VECTOR(1 downto 0);
type   GERROR is (NOERROR,ERRORA,ERRORB);
signal GROUP_ERR: GERROR;
  function ULV2BIT_TO_FRAME_MAC_STATES (L:STD_LOGIC_VECTOR(1 downto 0)) return FRAME_MAC_STATES is
  variable RESULT: FRAME_MAC_STATES;
  begin
    case L is
      when "00" =>
        RESULT := SEARCH ;
      when "01" =>
        RESULT := MATCH ;
      when "10" =>
        RESULT := FOUND ;
      when "11" =>
        RESULT := ERROR ;
      when others =>
        RESULT := SEARCH ;
    end case;
    return RESULT;
  end;

  function ULV3BIT_TO_MAC_STATES (L: STD_LOGIC_VECTOR(2 downto 0)) return MAC_STATES is
  variable RESULT: MAC_STATES;
  begin
    case L is
      when "000" =>
        RESULT := OUT_OF_SYNC ;
      when "001" =>
        RESULT := SEEN_ONCE ;
      when "010" =>
        RESULT := SEEN_TWICE ;
      when "011" =>
        RESULT := IN_SYNC ;
      when "100" =>
        RESULT := MISSED_ONCE ;
      when "101" =>
        RESULT := MISSED_TWICE ;
      when others =>
        RESULT := OUT_OF_SYNC ;
    end case;
    return RESULT;
  end;

  function FRAME_MAC_STATES_TO_ULV2BIT (L: FRAME_MAC_STATES) return STD_LOGIC_VECTOR is
  variable RESULT: STD_LOGIC_VECTOR(1 downto 0);
  begin
    case L is
      when SEARCH =>
        RESULT := "00" ;
      when MATCH =>
        RESULT := "01" ;
      when FOUND =>
        RESULT := "10" ;
      when ERROR =>
        RESULT := "11" ;
      when others =>
        RESULT := "UU" ;
    end case;
    return RESULT;
  end;

  function MAC_STATES_TO_ULV3BIT (L: MAC_STATES) return STD_LOGIC_VECTOR is
  variable RESULT: STD_LOGIC_VECTOR(2 downto 0);
  begin
    case L is
      when OUT_OF_SYNC =>
        RESULT := "000" ;
      when SEEN_ONCE =>
        RESULT := "001" ;
      when SEEN_TWICE =>
        RESULT := "010" ;
      when IN_SYNC =>
        RESULT := "011" ;
      when MISSED_ONCE =>
        RESULT := "100" ;
      when MISSED_TWICE =>
        RESULT := "101" ;
      when others =>
        RESULT := "UUU" ;
    end case;
    return RESULT;
  end;

  function PERSIST_MAC_STATES_TO_ULV2BIT (L: PERSIST_MAC_STATES) return STD_LOGIC_VECTOR is
  variable RESULT: STD_LOGIC_VECTOR(1 downto 0);
  begin
    case L is
      when SEARCH =>
        RESULT := "00" ;
      when MATCH =>
        RESULT := "01" ;
      when FOUND_TWICE =>
        RESULT := "10" ;
      when FROZEN =>
        RESULT := "11" ;
      when others =>
        RESULT := "UU" ;
    end case;
    return RESULT;
  end;

  function CYC_STATE_TO_ULV2BIT (X:CYC_STATE) return STD_LOGIC_VECTOR is
  variable RESULT: STD_LOGIC_VECTOR(1 downto 0); 
  begin
     case X is
       when ENABLED =>
         RESULT := "00";
       when SEEN_ONCE =>
         RESULT := "01";
       when SEEN_TWICE =>
         RESULT := "10";
       when DISABLED =>
         RESULT := "11";
     end case;
     return RESULT;
  end; 

  function ULV2BIT_TO_CYC_STATE(X:STD_LOGIC_VECTOR(1 downto 0)) return CYC_STATE is
  variable RESULT: CYC_STATE;
  begin
    case X is
      when "00" =>
        RESULT := ENABLED;
      when "01" =>
        RESULT := SEEN_ONCE;
      when "10" =>
        RESULT := SEEN_TWICE;
      when "11" =>
        RESULT := DISABLED;
      when others =>
        RESULT := ENABLED;
    end case;
    return RESULT;
  end;

  function ULV2BIT_TO_PERSIST_MAC_STATES (L:STD_LOGIC_VECTOR(1 downto 0)) return PERSIST_MAC_STATES is
  variable RESULT: PERSIST_MAC_STATES;
  begin 
    case L is
      when "00" =>
        RESULT := SEARCH ;
      when "01" =>
        RESULT := MATCH ;
      when "10" =>
        RESULT := FOUND_TWICE ;
      when "11" =>
        RESULT := FROZEN ;
      when others =>
        RESULT := SEARCH ;
    end case;
    return RESULT;
  end;

-- PSL default clock is rising_edge(OCTET_STROBE);

-- PSL sequence FRAME_STATE_SEARCH_TO_MATCH is
--     {FRAME_STATE = SEARCH ; FRAME_STATE = MATCH };
-- PSL Cover_FRAME_STATE_SEARCH_TO_MATCH : cover FRAME_STATE_SEARCH_TO_MATCH ;
-- PSL sequence FRAME_STATE_MATCH_TO_FOUND is
--     {FRAME_STATE = MATCH ; FRAME_STATE = FOUND };
-- PSL Cover_FRAME_STATE_MATCH_TO_FOUND : cover FRAME_STATE_MATCH_TO_FOUND ;
-- PSL sequence FRAME_STATE_FOUND_TO_ERROR is
--     {FRAME_STATE = FOUND ; FRAME_STATE = ERROR };
-- PSL Cover_FRAME_STATE_FOUND_TO_ERROR : cover FRAME_STATE_FOUND_TO_ERROR ;
-- PSL sequence FRAME_STATE_ERROR_TO_MATCH is
--     {FRAME_STATE = ERROR ; FRAME_STATE = MATCH };
-- PSL Cover_FRAME_STATE_ERROR_TO_MATCH : cover FRAME_STATE_ERROR_TO_MATCH ;
-- PSL sequence FRAME_STATE_ERROR_TO_FOUND is
--     {FRAME_STATE = ERROR ; FRAME_STATE = FOUND };
-- PSL Cover_FRAME_STATE_ERROR_TO_FOUND : cover FRAME_STATE_ERROR_TO_FOUND ;
-- PSL sequence FRAME_STATE_MATCH_TO_ERROR is
--     {FRAME_STATE = MATCH ; FRAME_STATE = ERROR };
-- PSL Cover_FRAME_STATE_MATCH_TO_ERROR : cover FRAME_STATE_MATCH_TO_ERROR ;

-- PSL sequence FAW_STATE_OUT_OF_SYNC_TO_SEEN_ONCE is
--     {FAW_STATE  = OUT_OF_SYNC ; FAW_STATE  = SEEN_ONCE } @ (FAW_POSITION'event and FAW_POSITION = '1');
-- PSL Cover_FAW_STATE_OUT_OF_SYNC_TO_SEEN_ONCE : cover FAW_STATE_OUT_OF_SYNC_TO_SEEN_ONCE ;
-- PSL sequence FAW_STATE_SEEN_ONCE_TO_SEEN_TWICE is
--     {FAW_STATE  = SEEN_ONCE ; FAW_STATE  = SEEN_TWICE } @ (FAW_POSITION'event and FAW_POSITION = '1');
-- PSL Cover_FAW_STATE_SEEN_ONCE_TO_SEEN_TWICE : cover FAW_STATE_SEEN_ONCE_TO_SEEN_TWICE ;
-- PSL sequence FAW_STATE_SEEN_TWICE_TO_IN_SYNC is
--     {FAW_STATE  = SEEN_TWICE; FAW_STATE  = IN_SYNC } @ (FAW_POSITION'event and FAW_POSITION = '1');
-- PSL Cover_FAW_STATE_SEEN_TWICE_TO_IN_SYNC : cover FAW_STATE_SEEN_TWICE_TO_IN_SYNC;
-- PSL sequence FAW_STATE_IN_SYNC_TO_MISSED_ONCE is
--     {FAW_STATE  = IN_SYNC ; FAW_STATE  = MISSED_ONCE } @ (FAW_POSITION'event and FAW_POSITION = '1');
-- PSL Cover_FAW_STATE_IN_SYNC_TO_MISSED_ONCE : cover FAW_STATE_IN_SYNC_TO_MISSED_ONCE ;
-- PSL sequence FAW_STATE_MISSED_ONCE_TO_MISSED_TWICE is
--     {FAW_STATE  = MISSED_ONCE ; FAW_STATE  = MISSED_TWICE } @ (FAW_POSITION'event and FAW_POSITION = '1');
-- PSL Cover_FAW_STATE_MISSED_ONCE_TO_MISSED_TWICE : cover FAW_STATE_MISSED_ONCE_TO_MISSED_TWICE;
-- PSL sequence FAW_STATE_MISSED_TWICE_TO_OUT_OF_SYNC is
--     {FAW_STATE  = MISSED_TWICE ; FAW_STATE  = OUT_OF_SYNC} @ (FAW_POSITION'event and FAW_POSITION = '1');
-- PSL Cover_FAW_STATE_MISSED_TWICE_TO_OUT_OF_SYNC : cover FAW_STATE_MISSED_TWICE_TO_OUT_OF_SYNC ;
-- PSL sequence FAW_STATE_MISSED_ONCE_TO_OUT_OF_SYNC is
--     {FAW_STATE  = MISSED_ONCE ; FAW_STATE  = OUT_OF_SYNC} @ (FAW_POSITION'event and FAW_POSITION = '1');
-- PSL Cover_FAW_STATE_MISSED_ONCE_TO_OUT_OF_SYNC : cover FAW_STATE_MISSED_ONCE_TO_OUT_OF_SYNC;
-- PSL sequence FAW_STATE_SEEN_ONCE_TO_OUT_OF_SYNC is
--     {FAW_STATE  = SEEN_ONCE ; FAW_STATE  = OUT_OF_SYNC } @ (FAW_POSITION'event and FAW_POSITION = '1');
-- PSL Cover_FAW_STATE_SEEN_ONCE_TO_OUT_OF_SYNC : cover FAW_STATE_SEEN_ONCE_TO_OUT_OF_SYNC ;
-- PSL sequence FAW_STATE_SEEN_TWICE_TO_OUT_OF_SYNC is
--     {FAW_STATE  = SEEN_TWICE ; FAW_STATE  = OUT_OF_SYNC } @ (FAW_POSITION'event and FAW_POSITION = '1');
-- PSL Cover_FAW_STATE_SEEN_TWICE_TO_OUT_OF_SYNC : cover FAW_STATE_SEEN_TWICE_TO_OUT_OF_SYNC ;

begin

-- VARIABLE MANAGER
-- The 10 bit variable counter, split into
-- two five bit sectors for speed improvement.
VARIABLE_COUNTER: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if COMMON_RST = '0' or RESET = '0' then
      VCOUNTA <= "00000";
    else
      VCOUNTA <= VCOUNTA + '1';
    end if;
    if RESET = '0' then
      VCOUNT_FULL <= '0';
    elsif VCOUNTA = "11110" then
      VCOUNT_FULL <= '1';
    else
      VCOUNT_FULL <= '0';
    end if;
    if COMMON_RST = '0' or RESET = '0' then
      VCOUNTB <= "00000";
    elsif VCOUNT_FULL = '1' then
      VCOUNTB <= VCOUNTB + '1';
    end if;
end process;
-- Generate the column and variable address
-- from the counter values.
VARIABLE_GEN: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      VARIABLE_NUMBER <= VCOUNT(3 downto 1);
    elsif VCOUNT(4) = '1' then
      VARIABLE_NUMBER <= not(VCOUNT(3 downto 1));
    else
      VARIABLE_NUMBER <= VCOUNT(3 downto 1);
    end if;
    if RESET = '0' then
      VARIABLE_COLUMN <= DELAYED_COLUMN;
    elsif VCOUNT(4 downto 1) = "0000" then 
      VARIABLE_COLUMN <= VCOUNT(9 downto 5); 
    else 
      VARIABLE_COLUMN <= DELAYED_COLUMN; 
    end if ;
end process;
-- Generate the write strobe for the variable RAM.
VARWR_STROBE: process
begin
  wait until FALLING_EDGE (CLOCK) ;
    if RESET = '0' then
      VARIABLE_WRITE <= '0' ;
    else
      case VCOUNTA is
      when "11111" =>
        VARIABLE_WRITE <= '0' ;
      when "00011" =>
        VARIABLE_WRITE <= '0' ;
      when "00101" =>
        VARIABLE_WRITE <= '0' ;
      when "00111" =>
        VARIABLE_WRITE <= '0' ;
      when "01001" =>
        VARIABLE_WRITE <= '0' ;
      when "01011" =>
        VARIABLE_WRITE <= '0' ;
      when "01101" =>
        VARIABLE_WRITE <= '0' ;
      when "01111" =>
        VARIABLE_WRITE <= '0' ;
      when others =>
        VARIABLE_WRITE <= '1' ;
      end case;
    end if ;
end process;
-- Generate variable strobes for the variable
-- manager.
VAR_RISING_STROBES: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      VAR_RD0 <= '1';
    elsif (VCOUNT(4 downto 0)) = "00000" then
      VAR_RD0 <= '0';
    else
      VAR_RD0 <= '1';
    end if;
    if RESET = '0' then
      VAR_RD1 <= '1';
    elsif (VCOUNT(4 downto 0)) = "11100" then
      VAR_RD1 <= '0';
    else
      VAR_RD1 <= '1';
    end if;
    if RESET = '0' then 
      VAR_RD2 <= '1';
    elsif (VCOUNT(4 downto 0)) = "11010" then
      VAR_RD2 <= '0';
    else
      VAR_RD2 <= '1';
    end if;
    if RESET = '0' then  
      VAR_RD3 <= '1';
    elsif (VCOUNT(4 downto 0)) = "11000" then
      VAR_RD3 <= '0';
    else
      VAR_RD3 <= '1';
    end if;
    if RESET = '0' then
      VAR_RD4 <= '1';
    elsif (VCOUNT(4 downto 0)) = "10110" then
      VAR_RD4 <= '0';
    else
      VAR_RD4 <= '1';
    end if;
    if RESET = '0' then 
      VAR_RD5 <= '1';
    elsif (VCOUNT(4 downto 0)) = "10100" then
      VAR_RD5 <= '0';
    else
      VAR_RD5 <= '1';
    end if;
    if RESET = '0' then  
      VAR_RD6 <= '1';
    elsif (VCOUNT(4 downto 0)) = "10010" then
      VAR_RD6 <= '0';
    else
      VAR_RD6 <= '1';
    end if;
    if RESET = '0' then   
      VAR_RD7 <= '1';
    elsif (VCOUNT(4 downto 0)) = "10000" then
      VAR_RD7 <= '0';
    else
      VAR_RD7 <= '1';
    end if;
    if (VCOUNT(4 downto 0)) = "01111" or RESET = '0' then
      DCOLUMN <= VCOUNT(9 downto 5);
    else
      DCOLUMN <= DCOLUMN;
    end if;
    if RESET = '0' then    
      OCTET_STROBE <= '0';
    elsif (VCOUNT(4 downto 0)) = "11111" then
      OCTET_STROBE <= '1';
    else
      OCTET_STROBE <= '0';
    end if;
    if RESET = '0' then
      FSWR_STROBE <= '0';
    elsif (VCOUNT(4 downto 0)) = "11110" then
      FSWR_STROBE <= '1';
    else
      FSWR_STROBE <= '0';
    end if;
    if RESET = '0' then 
      FSDAT_STROBE <= '0';
    elsif (VCOUNT(4 downto 1)) = "0000" then
      FSDAT_STROBE <= '1';
    else
      FSDAT_STROBE <= '0';
    end if;
    if RESET = '0' then  
      FSADDR_ENB <= '0';
    elsif (VCOUNT(4 downto 1)) = "0000" or (VCOUNT(4 downto 0)) = "11111"then
      FSADDR_ENB <= '1';
    else
      FSADDR_ENB <= '0';
    end if;
    if RESET = '0' then  
      UP_DATE_POINTER <= '0';
    elsif VCOUNT(9 downto 3) = "0000001" then
      UP_DATE_POINTER <= '1';
    else
      UP_DATE_POINTER <= '0';
    end if;
    if RESET = '0' then
      VARIABLE_READ <= '0';
      BIT_STROBE <= '0';
      CRC_STROBE <= '0';
    else
      case VCOUNTA is
      when "00000" =>
        VARIABLE_READ    <= '0' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '0';
      when "00001" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '1';
        CRC_STROBE <= '0';
      when "00101" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '1';
        CRC_STROBE <= '0';
      when "01001" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '1';
        CRC_STROBE <= '0';
      when "01101" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '1';
        CRC_STROBE <= '0';
      when "10000" =>
        VARIABLE_READ    <= '0' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '0';
      when "01111" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '0';
      when "10001" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '1';
        CRC_STROBE <= '0';
      when "10010" =>
        VARIABLE_READ    <= '0' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '0';
      when "10100" =>
        VARIABLE_READ    <= '0' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '0';
      when "10101" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '1';
        CRC_STROBE <= '0';
      when "10110" =>
        VARIABLE_READ    <= '0' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '0';
      when "11000" =>
        VARIABLE_READ    <= '0' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '0';
      when "11001" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '1';
        CRC_STROBE <= '0';
      when "11010" =>
        VARIABLE_READ    <= '0' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '1';
      when "11011" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '1';
      when "11100" =>
        VARIABLE_READ    <= '0' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '1';
      when "11101" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '1';
        CRC_STROBE <= '1';
      when "11111" =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '0';
      when others =>
        VARIABLE_READ    <= '1' ;
        BIT_STROBE <= '0';
        CRC_STROBE <= '0';
      end case;
    end if ;
end process;
-- DATA STORE
-- The incoming data store.
DATA_STORE: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      REGISTER_CONTENTS <= "00000000000";
    elsif BIT_STROBE = '1' then
      REGISTER_CONTENTS <= REGISTER_CONTENTS(9 downto 0) & DATA_IN;
    end if;
end process;
-- STATE MACHINE STROBES
-- Generates the necessary strobes for the state 
-- machines.
GENERATE_COMPARES: process
begin
  wait until RISING_EDGE (CLOCK);
    -- Test for FAW pattern in Register.
    if RESET = '0' then
      COMPARE_FAW <= '0';
    elsif REGISTER_CONTENTS(7 downto 0) = "00011011" then
      COMPARE_FAW <= '1';
    else
      COMPARE_FAW <= '0';
    end if;
    -- Test for IC SYNC pattern in Register.
    if RESET = '0' then
      COMPARE_ICHAN <= '0';
    elsif REGISTER_CONTENTS(7 downto 0) = "01111111" then
      COMPARE_ICHAN <= '1';
    else
      COMPARE_ICHAN <= '0';
    end if;
    -- Test Octet Counter for the position of
    -- the FAW octet.
    if RESET = '0' then 
      FAW_POSITION <= '0';
    elsif OCTET_COUNT = "00000000" then
      FAW_POSITION <= '1';
    else
      FAW_POSITION <= '0';
    end if;
    -- Test Octet Counter for the position of
    -- the IC frame.
    if RESET = '0' then  
      IC_POSITION <= '0';
    elsif TEST_MODE = '1' and OCTET_COUNT(3 downto 0) = "0100" then
      IC_POSITION <= '1';
    elsif OCTET_COUNT = "01000000" then
      IC_POSITION <= '1';
    else
      IC_POSITION <= '0';
    end if;
    -- Test Octet Counter for the position of
    -- the FRAME COUNT octet.
    if RESET = '0' then
      FRAME_POSITION <= '0';
    elsif TEST_MODE = '1' and OCTET_COUNT(3 downto 0) = "1000" then
      FRAME_POSITION <= '1';
    elsif OCTET_COUNT = "10000000" then
      FRAME_POSITION <= '1';
    else
      FRAME_POSITION <= '0';
    end if;
    -- Test Mode Value for CRC Octet
    if RESET = '0' then
      CRC_POSITION <= '0';
    elsif TEST_MODE = '1' and OCTET_COUNT(3 downto 0) = "1100" then
      CRC_POSITION <= '1';
    elsif OCTET_COUNT = "11000000" then
      CRC_POSITION <= '1';
    else
      CRC_POSITION <= '0';
    end if;
    -- Test IC Counter for the start on the
    -- IC frame.
    if RESET = '0' then
      IC_SYNC_POSITION <= '0';
    elsif TEST_MODE = '1' and ICHAN_COUNT(1 downto 0) = "00" then
      IC_SYNC_POSITION <= '1';
    elsif ICHAN_COUNT = "0000" then
      IC_SYNC_POSITION <= '1';
    else
      IC_SYNC_POSITION <= '0';
    end if;
    -- Test IC counter for the position of
    -- the channel ID
    if RESET = '0' then
      CHAN_ID_POSITION <= '0';
    elsif TEST_MODE = '1' and ICHAN_COUNT(1 downto 0) = "01" then
      CHAN_ID_POSITION <= '1';
    elsif ICHAN_COUNT = "0001" then
      CHAN_ID_POSITION <= '1';
    else
      CHAN_ID_POSITION <= '0';
    end if;
    -- Test IC counter for the position of
    -- the group ID
    if RESET = '0' then
      GROUP_ID_POSITION <= '0';
    elsif TEST_MODE = '1' and ICHAN_COUNT(1 downto 0) = "10" then
      GROUP_ID_POSITION <= '1';
    elsif ICHAN_COUNT = "0010" then
      GROUP_ID_POSITION <= '1';
    else
      GROUP_ID_POSITION <= '0';
    end if;
end process;
-- IC STATE MACHINE
-- Information channel state machine. If the FAW state 
-- machine is out of sync and the ic state machine is in
-- sync then master channel negotiation has been reached.
-- If the faw state machine is in sync and the ic state 
-- machine is in sync then multi-frame sync has been found.
ICHAN_STATE_MACHINE: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      ICHAN_STATE <= SEARCH ;
      ICHAN_RESET <= '0';
    elsif VAR_RD4 = '0' then
      ICHAN_STATE <= IN_IC_STATE;
    elsif OCTET_STROBE = '1' then
      case ICHAN_STATE is
      when SEARCH =>
        if COMPARE_ICHAN = '1' then
          if FAW_SYNC_FOUND = '0' then
            ICHAN_STATE <= MATCH;
            ICHAN_RESET <= '1';
          elsif IC_POSITION = '1' then
            ICHAN_STATE <= MATCH;
            ICHAN_RESET <= '1';
          end if;
        else
          ICHAN_RESET <= '0';
          ICHAN_STATE <= SEARCH;
        end if;
      when MATCH =>
        if FAW_SYNC_FOUND = '0' then
          if IC_SYNC_POSITION = '1' then
            if COMPARE_ICHAN = '1' then
              ICHAN_STATE <= FOUND;
            else
              ICHAN_STATE <= SEARCH;
            end if;
          else
            ICHAN_STATE <= MATCH;
          end if;
        elsif IC_POSITION = '1' and IC_SYNC_POSITION = '1' then
          if COMPARE_ICHAN = '1' then
            ICHAN_STATE <= FOUND;
          else
            ICHAN_STATE <= SEARCH;
          end if;
        else
          ICHAN_STATE <= MATCH;
        end if;
        ICHAN_RESET <= '0';
      when FOUND =>
        if FAW_SYNC_FOUND = '0' then
          if IC_SYNC_POSITION = '1' then
            if COMPARE_ICHAN = '1' then
              ICHAN_STATE <= FOUND;
            else
              ICHAN_STATE <= ERROR;
            end if;
          else
            ICHAN_STATE <= FOUND;
          end if;
        -- If multi-frames and data mode enabled
        elsif DATA_MODE = '1' then
          ICHAN_STATE <= FOUND;
        elsif IC_POSITION = '1' and IC_SYNC_POSITION = '1' then
          if COMPARE_ICHAN = '1' then
            ICHAN_STATE <= FOUND;
          else
            ICHAN_STATE <= ERROR;
          end if;
        else
          ICHAN_STATE <= FOUND;
        end if;
        ICHAN_RESET <= '0';
      when ERROR =>
        if FAW_SYNC_FOUND = '0' then
          if IC_SYNC_POSITION = '1' then
            if COMPARE_ICHAN = '1' then
              ICHAN_STATE <= FOUND;
            else
              ICHAN_STATE <= SEARCH;
            end if;
          else
            ICHAN_STATE <= ERROR;
          end if;
        elsif IC_POSITION = '1' and IC_SYNC_POSITION = '1' then
          if COMPARE_ICHAN = '1' then
            ICHAN_STATE <= FOUND;
          else
            ICHAN_STATE <= SEARCH;
          end if;
        else
          ICHAN_STATE <= ERROR;
        end if;
        ICHAN_RESET <= '0';
      end case;
    end if;
    case ICHAN_STATE is
      when SEARCH =>
        IC_SYNC_FOUND <= '0';
      when MATCH | FOUND | ERROR =>
        IC_SYNC_FOUND <= '1';
    end case;
end process;
-- FAW STATE MACHINE
-- The faw state machine is the first in the series, if
-- it is in sync then multi-frame sync has been found.
FAW_STATE_MACHINE: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      FAW_STATE <= OUT_OF_SYNC ;
      OCTET_COUNT_RESET <= '0';
    elsif VAR_RD6 = '0' then
      FAW_STATE <= IN_FAW_STATE;
    elsif OCTET_STROBE = '1' then
      case FAW_STATE is
      when OUT_OF_SYNC =>
        if COMPARE_FAW = '1' then
          OCTET_COUNT_RESET <= '1';
          FAW_STATE <= SEEN_ONCE;
        else
          OCTET_COUNT_RESET <= '0';
          FAW_STATE <= OUT_OF_SYNC;
        end if;
      when SEEN_ONCE =>
        if FAW_POSITION = '1' then
          if COMPARE_FAW = '1' then
            FAW_STATE <= SEEN_TWICE;
          else
            FAW_STATE <= OUT_OF_SYNC;
          end if;
        end if;
        OCTET_COUNT_RESET <= '0';
      when SEEN_TWICE =>
        if FAW_POSITION = '1' then
          if COMPARE_FAW = '1' then
            FAW_STATE <= IN_SYNC;
          else
            FAW_STATE <= OUT_OF_SYNC;
          end if;
        end if;
        OCTET_COUNT_RESET <= '0';
      when IN_SYNC =>
        if DATA_MODE = '1' then
          FAW_STATE <= IN_SYNC;
        elsif FAW_POSITION = '1' then
          if COMPARE_FAW = '1' then
            FAW_STATE <= IN_SYNC;
          else
            FAW_STATE <= MISSED_ONCE;
          end if;
        end if;
        OCTET_COUNT_RESET <= '0';
      when MISSED_ONCE =>
        if FAW_POSITION = '1' then
          if COMPARE_FAW = '1' then
            FAW_STATE <= IN_SYNC;
          else
            FAW_STATE <= MISSED_TWICE;
          end if;
        end if;
        OCTET_COUNT_RESET <= '0';
      when MISSED_TWICE =>
        if FAW_POSITION = '1' then
          if COMPARE_FAW = '1' then
            FAW_STATE <= IN_SYNC;
          else
            FAW_STATE <= OUT_OF_SYNC;
          end if;
        end if;
        OCTET_COUNT_RESET <= '0';
      end case;
    end if;
    case FAW_STATE is
      when OUT_OF_SYNC | SEEN_ONCE | SEEN_TWICE =>
        FAW_SYNC_FOUND <= '0';
      when IN_SYNC | MISSED_ONCE | MISSED_TWICE =>
        FAW_SYNC_FOUND <= '1';
    end case;
end process;
-- OCTET COUNTER
-- Keeps track of the current octet be processed
OCTET_COUNTER: process
begin
  wait until RISING_EDGE (CLOCK);
    if (OCTET_COUNT_RESET = '1' and VAR_RD0 = '0') or RESET = '0' then
      OCOUNTA <= "0000" ;
    elsif VAR_RD5 = '0' then
      OCOUNTA <= VARIABLE_RESTORE(3 downto 0) ;
    elsif VAR_RD4 = '0' then
      OCOUNTA <= OCOUNTA + '1' ;
    end if;
    if RESET = '0' then
      OFULL <= '0';
    elsif OCOUNTA = "1111" then
      OFULL <= '1';
    else
      OFULL <= '0';
    end if;
    if (OCTET_COUNT_RESET = '1' and VAR_RD0 = '0') or RESET = '0' or TEST_MODE = '1' then
      OCOUNTB <= "0000" ;
    elsif VAR_RD5 = '0' then
      OCOUNTB <= VARIABLE_RESTORE(7 downto 4) ;
    elsif VAR_RD4 = '0' and OFULL = '1' then
      OCOUNTB <= OCOUNTB + '1' ;
    end if;
end process;
-- ICHAN COUNTER
-- Keeps track of the current octet within the information
-- message.
ICHAN_COUNTER: process
begin
  wait until RISING_EDGE (CLOCK);
    if (ICHAN_RESET = '1' and VAR_RD0 = '0') or RESET = '0' then
      ICOUNT <= "0000" ;
    elsif VAR_RD6 = '0' then
      ICOUNT <= VARIABLE_RESTORE(3 downto 0);
    elsif VAR_RD1 = '0' then
      if FAW_SYNC_FOUND = '1' then
        if IC_POSITION = '1' then
          ICOUNT <= ICOUNT + '1' ;
        end if;
      else
        ICOUNT <= ICOUNT + '1' ;
      end if;
    end if;
end process;
-- VARIABLE MULTIPLEXER
-- Enables the storage of all of the variables.
VARIABLE_MUX: process(VARIABLE_RESET,VARIABLE_NUMBER,CRC,GROUP_STORE,STATES_CRC,CHANID_STORE,
                      STATES_GROUP,STATES_CHAN_ID,STATES_FRAME,STATES_ICHAN,OCTET_COUNT,
                      STATES_FAW,ICHAN_COUNT,STORE_FRAMES)
begin
if VARIABLE_RESET = '1' then
  VARIABLE_SAVE <= "00000000";
else
  case VARIABLE_NUMBER is
  when "000" =>
    VARIABLE_SAVE <= "1111" & CRC;
  when "001" =>
    VARIABLE_SAVE <= "11" & GROUP_STORE;
  when "010" =>
    VARIABLE_SAVE <= STATES_CRC & '1' & CHANID_STORE;
  when "011" =>
    VARIABLE_SAVE <= STATES_GROUP & "1111" & STATES_CHAN_ID;
  when "100" =>
    VARIABLE_SAVE <= "11" & STATES_FRAME & "11" & STATES_ICHAN;
  when "101" =>
    VARIABLE_SAVE <= OCTET_COUNT;
  when "110" =>
    VARIABLE_SAVE <= '1' & STATES_FAW & ICHAN_COUNT;
  when "111" =>
    VARIABLE_SAVE <= "11" & STORE_FRAMES;
  when others =>
    null;
  end case;
end if;
end process;
-- FRAME COUNTER
-- Keeps track of the current frame number for the octet
-- being processed.
FRAME_COUNTER: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      FRCOUNTA <= "000";
    elsif VAR_RD7 = '0' then
      FRCOUNTA <= VARIABLE_RESTORE(2 downto 0) ;
    elsif VAR_RD3 = '0' and FAW_POSITION = '1' then
      FRCOUNTA <= FRCOUNTA + '1' ;
    end if;
    if RESET = '0' then
      FRFULL <= '0';
    elsif FRCOUNTA = "111" then
      FRFULL <= '1';
    else
      FRFULL <= '0';
    end if;
    if RESET = '0' then
      FRCOUNTB <= "000";
    elsif VAR_RD7 = '0' then
      FRCOUNTB <= VARIABLE_RESTORE(5 downto 3) ;
    elsif VAR_RD3 = '0' and FRFULL = '1' and FAW_POSITION = '1' then
      FRCOUNTB <= FRCOUNTB + '1' ;
    end if;
end process;
-- FRAME STATE MACHINE
-- Ensures that the frame number from the line is
-- correct and incrementing.
FRAM_STATE_MACHINE: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      FRAME_STATE <= SEARCH ;
    elsif VAR_RD4 = '0' then
      FRAME_STATE <= IN_FRAME_STATE;
    elsif OCTET_STROBE = '1' then
      case FRAME_STATE is
      when SEARCH =>
        if FAW_SYNC_FOUND = '1' and FRAME_POSITION = '1' then
          if FRAME_MATCHED = '1' then
            FRAME_STATE       <= MATCH ;
          else
            FRAME_STATE       <= SEARCH ;
          end if;
        else
          FRAME_STATE       <= SEARCH ;
        end if ;
      when MATCH =>
        if FAW_SYNC_FOUND = '1' and FRAME_POSITION = '1' then
          if FRAME_MATCHED = '1' then
            FRAME_STATE       <= FOUND ;
          else
            FRAME_STATE       <= SEARCH ;
          end if;
        else
          FRAME_STATE       <= MATCH ;
        end if ;
      when FOUND =>
        if DATA_MODE = '1' then
          FRAME_STATE       <= FOUND ;
        elsif FAW_SYNC_FOUND = '1' and FRAME_POSITION = '1' then
          if FRAME_MATCHED = '1' then
            FRAME_STATE       <= FOUND ;
          else
            FRAME_STATE       <= ERROR ;
          end if;
        else
          FRAME_STATE       <= FOUND ;
        end if ;
      when ERROR =>
        if FAW_SYNC_FOUND = '1' and FRAME_POSITION = '1' then
          if FRAME_MATCHED = '1' then
            FRAME_STATE       <= FOUND ;
          else
            FRAME_STATE       <= SEARCH ;
          end if;
        else
          FRAME_STATE       <= ERROR ;
        end if ;
      end case;
    end if;
    case FRAME_STATE is
      when SEARCH | MATCH =>
        FRAME_SYNC_FOUND <= '0';
      when FOUND | ERROR =>
        FRAME_SYNC_FOUND <= '1';
    end case;
end process;
-- FRAME COUNT STORE
-- Decides whether to take the value from line
-- or increment the current one.
FRAME_COUNT_STORE: process
begin
  wait until RISING_EDGE (CLOCK);
    -- Test for FRAME count in Register.
    if RESET = '0' then
      FRAME_MATCHED <= '0';
    elsif REGISTER_CONTENTS(6 downto 1) = FRAMES then
      FRAME_MATCHED <= '1';
    else
      FRAME_MATCHED <= '0';
    end if;
    -- If the state machine has not found
    -- sync save the on-line value of frames
    if RESET = '0' then
      STORE_FRAMES <= FRAMES;
    elsif FAW_SYNC_FOUND = '1' and FRAME_SYNC_FOUND = '0'
       and FRAME_POSITION = '1' then
      STORE_FRAMES <= REGISTER_CONTENTS(10 downto 5);
    else
      STORE_FRAMES <= FRAMES;
    end if;
end process;
-- CHANNEL ID STATE MACHINE
-- Searches for the channel id transmitted in 
-- the information message and freezes it.
CHAN_STATE_MACHINE: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      CHAN_ID_STATE <= SEARCH ;
    elsif VAR_RD3 = '0' then
      CHAN_ID_STATE <= IN_CHAN_ID_STATE;
    elsif OCTET_STROBE = '1' then
        if DATA_MODE = '1' and CHAN_ID_STATE = FROZEN then
          CHAN_ID_STATE <= FROZEN;
        elsif FAW_SYNC_FOUND = '1' then
          if IC_SYNC_FOUND = '1' then
            if IC_POSITION = '1' and CHAN_ID_POSITION = '1' then
              if CHAN_ID_MATCHED = '1' then
                case CHAN_ID_STATE is
                when SEARCH =>
                  CHAN_ID_STATE <= MATCH;
                when MATCH =>
                  CHAN_ID_STATE <= FOUND_TWICE;
                when FOUND_TWICE =>
                  CHAN_ID_STATE <= FROZEN;
                when FROZEN =>
                  CHAN_ID_STATE <= FROZEN;
                end case;
              else
                case CHAN_ID_STATE is
                when FROZEN =>
                  CHAN_ID_STATE <= FROZEN;
                when others =>
                  CHAN_ID_STATE <= SEARCH;
                end case;
              end if;
            end if;
          else
            CHAN_ID_STATE <= SEARCH;
          end if;
        else
          if IC_SYNC_FOUND = '1' then
            if CHAN_ID_POSITION = '1' then
              if CHAN_ID_MATCHED = '1' then
                case CHAN_ID_STATE is
                when SEARCH =>
                  CHAN_ID_STATE <= MATCH;
                when MATCH =>
                  CHAN_ID_STATE <= FOUND_TWICE;
                when FOUND_TWICE =>
                  CHAN_ID_STATE <= FROZEN;
                when FROZEN =>
                  CHAN_ID_STATE <= FROZEN;
                end case;
              else
                case CHAN_ID_STATE is
                when FROZEN =>
                  CHAN_ID_STATE <= FROZEN;
                when others =>
                  CHAN_ID_STATE <= SEARCH;
                end case;
              end if;
            end if;
          else
            CHAN_ID_STATE <= SEARCH;
          end if;
        end if ;
    end if;
    case CHAN_ID_STATE is
      when SEARCH | MATCH | FOUND_TWICE =>
        CHAN_ID_SYNC <= '0';
      when FROZEN =>
        CHAN_ID_SYNC <= '1';
    end case;
end process;
-- CHANNEL ID STORE
-- Keeps track of the current channel id loading from 
-- the line if in error.
CHANNEL_ID_STORE: process
begin
  wait until RISING_EDGE (CLOCK);
    -- Test for Channel ID in Register.
    if RESET = '0' then
      CHAN_ID_MATCHED <= '0';
    elsif REGISTER_CONTENTS(5 downto 1) = CHANID_STORE then
      CHAN_ID_MATCHED <= '1';
    else
      CHAN_ID_MATCHED <= '0';
    end if;
    -- If the state machine has not found
    -- sync save the on-line value of channel ID
    if RESET = '0' then
      CHANID_STORE <= "00000";
    elsif VAR_RD2 = '0' then
      CHANID_STORE <= VARIABLE_RESTORE(4 downto 0);
    elsif VAR_RD0 = '0' and CHAN_ID_SYNC = '0' then
      if FAW_SYNC_FOUND = '1' then
        if IC_SYNC_FOUND = '1' then
          if IC_POSITION = '1' and CHAN_ID_POSITION = '1' then
            CHANID_STORE(4 downto 0) <= REGISTER_CONTENTS(5 downto 1);
          else
            CHANID_STORE <= CHANID_STORE;
          end if;
        else
          CHANID_STORE <= "11111";
        end if;
      else
        if IC_SYNC_FOUND = '1' then
          if CHAN_ID_POSITION = '1' then
            CHANID_STORE(4 downto 0) <= REGISTER_CONTENTS(5 downto 1);
          else
            CHANID_STORE <= CHANID_STORE;
          end if;
        else
          CHANID_STORE <= "11111";
        end if;
      end if;
    else
      CHANID_STORE <= CHANID_STORE;
    end if;
end process;
-- CRC CHECKER
-- Calculates the CRC4 over 255 octets and
-- then compares it with the value sent from 
-- the transmitter.
process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      CRC <= "0000";
      CRC_RESET <= '0';
      CRC_COMPARE <= "0000";
      CRC_RESULT <= '0';
    elsif VAR_RD0 = '0' then               -- Store retrieved variable at
                                           -- begin of timeslot
      CRC         <= VARIABLE_RESTORE(3 downto 0);
      CRC_COMPARE <= VARIABLE_RESTORE(3 downto 0);
    elsif CRC_RESET_STROBE = '1' then      -- reset CRC to zero
      CRC <= "0000";
      CRC_RESET <= '0';
    elsif CRC_COMPARE_STROBE = '1' then    -- compare CRC values
      if CRC_STORE = CRC_COMPARE then      -- if CRC check passes
        CRC_RESULT <= '1';
        CRC_RESET <= '1';
      else                                 -- if CRC check fails
        CRC_RESULT <= '0';
        CRC_RESET <= '1';
      end if;
    elsif BIT_STROBE = '1' then            -- compute CRC
      CRC(3) <= DATA_IN xor CRC(0);
      CRC(2) <= CRC(3) xor (CRC(0) xor DATA_IN);
      CRC(1) <= CRC(2);
      CRC(0) <= CRC(1);
    end if;
    if RESET = '0' then
      CRC_STORE <= "0000";
    elsif BIT_STROBE = '1' then
--    CRC_STORE <= CRC_STORE(2 downto 0) & DATA_IN;
      CRC_STORE <= DATA_IN & CRC_STORE(3 downto 1);
    end if;
    if RESET = '0' then
      CRCSTATE <= ENABLED;
    elsif VAR_RD2 = '0' then
      CRCSTATE <= IN_CRC_STATE;
    elsif CRC_STORE = "1111" and CRC_COMPARE_STROBE = '1'
                and CRCSTATE = ENABLED then
      CRCSTATE <= SEEN_ONCE;
    elsif CRC_STORE = "1111" and CRC_COMPARE_STROBE = '1'
              and CRCSTATE = SEEN_ONCE then     
      CRCSTATE <= SEEN_TWICE;
    elsif CRC_STORE = "1111" and CRC_COMPARE_STROBE = '1'
             and CRCSTATE = SEEN_TWICE then    
      CRCSTATE <= DISABLED;
    elsif CRC_STORE = "1111" and CRC_COMPARE_STROBE = '1'
             and CRCSTATE = DISABLED then
      CRCSTATE <= DISABLED;
    elsif CRC_COMPARE_STROBE = '1' then
      CRCSTATE <= ENABLED;
    end if;
end process;
process (CRCSTATE)
  begin
    if CRCSTATE = ENABLED then
      CRC_ENABLED <= '1';
    else
      CRC_ENABLED <= '0';
    end if;
end process;
process (CRC_STROBE,CRC_POSITION,VAR_RD1,CRC_RESET)
begin
  if CRC_STROBE = '1' and CRC_POSITION = '1' and VAR_RD1 = '0' then
    CRC_COMPARE_STROBE <= '1';
  else
    CRC_COMPARE_STROBE <= '0';
  end if;
  if CRC_STROBE = '1' and CRC_POSITION = '1' and CRC_RESET = '1' then
    CRC_RESET_STROBE <= '1';
  else
    CRC_RESET_STROBE <= '0';
  end if;
end process;
-- ADDRESS GENERATOR
-- Produces the strobes for the frame store access and
-- modifies the channel id.
FSTORE_STROBES: process(CHAN_ID_SYNC,FSWR_STROBE,FSDAT_STROBE)
begin
    if CHAN_ID_SYNC = '1' then
      FS_WRITE <= not(FSWR_STROBE);
      FSDATENB_STROBE <= FSDAT_STROBE;
    else
      FS_WRITE <= '1';
      FSDATENB_STROBE <= '0';
    end if;
end process;
MODIFY_CHANNEL: process(CHANID_STORE)
begin
    case CHANID_STORE is
    when "00000" =>
      CHANNEL_ID <= "00000";
    when "00001" =>
      CHANNEL_ID <= "00000";
    when "00010" =>
      CHANNEL_ID <= "00001";
    when others =>
      CHANNEL_ID <= CHANID_STORE;
    end case;
end process;
-- POINTER GENERTOR
-- Produces the row pointer to the most delayed
-- channel.
-- Have deleted ADD00 to ADD12 because only the MSB
-- of the calculation is used.
-- Have deleted C013 as it is unused.
VCC <= '1';
A <= CALCULATED_VALUE;
B <= FRAMES & OCTET_COUNT;
ADD13 <= A(13) xor not(B(13)) xor CO12;
CO00  <= (A(0)  nand not(B(0)))  xor ( VCC  nand (A(0)  xor not(B(0))));
CO01  <= (A(1)  nand not(B(1)))  xor ( CO00 nand (A(1)  xor not(B(1))));
CO03  <= (A(3)  nand not(B(3)))  xor ( CO02 nand (A(3)  xor not(B(3))));
CO04  <= (A(4)  nand not(B(4)))  xor ( CO03 nand (A(4)  xor not(B(4))));
CO05  <= (A(5)  nand not(B(5)))  xor ( CO04 nand (A(5)  xor not(B(5))));
CO07  <= (A(7)  nand not(B(7)))  xor ( CO06 nand (A(7)  xor not(B(7))));
CO08  <= (A(8)  nand not(B(8)))  xor ( CO07 nand (A(8)  xor not(B(8))));
CO09  <= (A(9)  nand not(B(9)))  xor ( CO08 nand (A(9)  xor not(B(9))));
CO11  <= (A(11) nand not(B(11))) xor ( CO10 nand (A(11) xor not(B(11))));
CO12  <= (A(12) nand not(B(12))) xor ( CO11 nand (A(12) xor not(B(12))));
CALC_POINTER: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      CO02 <= '0';
      CO06 <= '0';
      CO10 <= '0';
    else
      CO02 <= (A(2)  nand not(B(2)))  xor ( CO01 nand (A(2)  xor not(B(2))));
      CO06 <= (A(6)  nand not(B(6)))  xor ( CO05 nand (A(6)  xor not(B(6))));
      CO10 <= (A(10) nand not(B(10))) xor ( CO09 nand (A(10) xor not(B(10))));
    end if;
    if RESET = '0' then
      CALCULATED_VALUE <= "00000000000000";
    elsif STORE_FIRST_VALUE = '1' then
      CALCULATED_VALUE <= FRAMES & OCTET_COUNT ;
    elsif OCTET_STROBE = '1' then
      if ( ADD13 = '0' and FRAME_SYNC_FOUND = '1') or
         ( ADD13 = '0' and  IC_SYNC_FOUND = '1' and FAW_SYNC_FOUND = '0' ) then
        CALCULATED_VALUE <= FRAMES & OCTET_COUNT ;
      else
        CALCULATED_VALUE <= CALCULATED_VALUE;
      end if;
    end if;
    if RESET = '0' then
      ONE_SHOT <= '0';
      STORED_VALUE <= "00000000000000";
    elsif UP_DATE_POINTER = '1' then
      ONE_SHOT <= '0' ;
      STORED_VALUE <= CALCULATED_VALUE;
    elsif ( VAR_RD3 = '0' and FRAME_SYNC_FOUND = '1' ) or 
    ( VAR_RD3 = '0' and IC_SYNC_FOUND = '1' and FAW_SYNC_FOUND = '0' ) then
      ONE_SHOT <= '1';
      STORED_VALUE <= STORED_VALUE;
    else
      ONE_SHOT <= ONE_SHOT;
      STORED_VALUE <= STORED_VALUE;
    end if;
    RETIME_ONE_SHOT <= ONE_SHOT ;
    STORE_FIRST_VALUE <= ONE_SHOT and not(RETIME_ONE_SHOT);
end process;
-- FRAME STORE DATA
STORE_FLAGS: process (FAW_POSITION,CRC_POSITION,DATA_MODE,CHAN_ID_SYNC,
                      FRAME_SYNC_FOUND,CRC_ENABLED,CRC_RESULT,
                      REGISTER_CONTENTS(1 downto 0))
variable SWITCH: STD_LOGIC_VECTOR(3 downto 0);
begin
SWITCH := FAW_POSITION & CRC_POSITION & DATA_MODE & FRAME_SYNC_FOUND;
  case SWITCH is
    when "1001" =>
      FRAME_STORE_DATA(7) <= FRAME_SYNC_FOUND;
      FRAME_STORE_DATA(6) <= CHAN_ID_SYNC;
    when "0101" =>
      FRAME_STORE_DATA(7) <= CRC_RESULT; 
      FRAME_STORE_DATA(6) <= CRC_ENABLED;
    when "0010" =>
      FRAME_STORE_DATA(7) <= REGISTER_CONTENTS(0); 
      FRAME_STORE_DATA(6) <= REGISTER_CONTENTS(1);
    when "0011" =>
      FRAME_STORE_DATA(7) <= REGISTER_CONTENTS(0); 
      FRAME_STORE_DATA(6) <= REGISTER_CONTENTS(1);
    when others =>
      FRAME_STORE_DATA(7) <= REGISTER_CONTENTS(0); 
      FRAME_STORE_DATA(6) <= REGISTER_CONTENTS(1);
  end case;
end process;
MASTER_FLAGS: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      MASTER_CHANNEL <= '0';
    elsif CHANNEL_ID = "00000" then
      MASTER_CHANNEL <= '1';
    else
      MASTER_CHANNEL <= '0';
    end if;
    if RESET = '0' then
      MASTER_CID_SYNC <= '0';
      MASTER_FRAME_SYNC <= '0';
    elsif OCTET_STROBE = '1' and MASTER_CHANNEL = '1' then
      MASTER_CID_SYNC <= CHAN_ID_SYNC;
      MASTER_FRAME_SYNC <= FRAME_SYNC_FOUND;
    end if;
end process;
-- IOM INTERFACE
-- Takes data from the IOM interface and switches it into
-- the first two slots of the common bus.
IOM_CLOCK: process
begin
  wait until RISING_EDGE (IOM_DCK) ;
    if RESET = '0' then
      IOMBITS <= "0000000000000000";
    elsif (IOM_SDS1 = '1' or IOM_SDS2 = '1') and IOM_ENABLE = '1' then
      IOMBITS <= IOMBITS(14 downto 0) & IOM_DD ;
    end if;
    if RESET = '0' then
      IOM_RETIME_ONE <= '0';
      IOM_RETIME_TWO <= '0';
    else
      IOM_RETIME_ONE <= IOM_SDS2 ; 
      IOM_RETIME_TWO <= not(IOM_RETIME_ONE);
    end if;
    if IOM_RESET = '1' or RESET = '0' then
      IOM_ENABLE <= '1' ; 
    else 
      IOM_ENABLE <= not(IOM_ENABLE); 
    end if ;
end process;
-- Common bus reset generation
COM_RESET: process
begin
  wait until RISING_EDGE (CLOCK) ;
    if RESET = '0' then
      RETIME_PRE8M <= '0';
      JITTER_PULSE <= '0';
    else
      RETIME_PRE8M <= not(PRE8M);
      JITTER_PULSE <= RETIME_PRE8M nand PRE8M;
    end if;
    if RESET = '0' then
      JITTER_RESET <= '0';
    elsif JITTER_PULSE = '0' then
      JITTER_RESET <= IOM_SDS2;
    end if;
    if RESET = '0' then
      RETIME_FCSA <= '0';
      RETIME_FCSB <= '0';
      COMMON_RST  <= '1';
    else  
      RETIME_FCSA <= JITTER_RESET ;
      RETIME_FCSB <= RETIME_FCSA ;
      COMMON_RST <= not(RETIME_FCSA) nand RETIME_FCSB;
    end if;
end process;
DECODE_COUNT: process (VCOUNT,IOM_POINTER,DATA_CLAMP,IOMBITS)
begin
   case VCOUNT is
     when "0000000000" | "0000000001" | "0000000010" |
          "0000000011" => IOM_POINTER <= "0000"; DATA_CLAMP <= '0';
     when "0000000100" | "0000000101" | "0000000110" |
          "0000000111" => IOM_POINTER <= "0001"; DATA_CLAMP <= '0';
     when "0000001000" | "0000001001" | "0000001010" |
          "0000001011" => IOM_POINTER <= "0010"; DATA_CLAMP <= '0';
     when "0000001100" | "0000001101" | "0000001110" |
          "0000001111" => IOM_POINTER <= "0011"; DATA_CLAMP <= '0';
     when "0000010000" | "0000010001" | "0000010010" |
          "0000010011" => IOM_POINTER <= "0100"; DATA_CLAMP <= '0';
     when "0000010100" | "0000010101" | "0000010110" |
          "0000010111" => IOM_POINTER <= "0101"; DATA_CLAMP <= '0';
     when "0000011000" | "0000011001" | "0000011010" |
          "0000011011" => IOM_POINTER <= "0110"; DATA_CLAMP <= '0';
     when "0000011100" | "0000011101" | "0000011110" |
          "0000011111" => IOM_POINTER <= "0111"; DATA_CLAMP <= '0';
     when "0000100000" | "0000100001" | "0000100010" |
          "0000100011" => IOM_POINTER <= "1000"; DATA_CLAMP <= '0';
     when "0000100100" | "0000100101" | "0000100110" |
          "0000100111" => IOM_POINTER <= "1001"; DATA_CLAMP <= '0';
     when "0000101000" | "0000101001" | "0000101010" |
          "0000101011" => IOM_POINTER <= "1010"; DATA_CLAMP <= '0';
     when "0000101100" | "0000101101" | "0000101110" |
          "0000101111" => IOM_POINTER <= "1011"; DATA_CLAMP <= '0';
     when "0000110000" | "0000110001" | "0000110010" |
          "0000110011" => IOM_POINTER <= "1100"; DATA_CLAMP <= '0';
     when "0000110100" | "0000110101" | "0000110110" |
          "0000110111" => IOM_POINTER <= "1101"; DATA_CLAMP <= '0';
     when "0000111000" | "0000111001" | "0000111010" |
          "0000111011" => IOM_POINTER <= "1110"; DATA_CLAMP <= '0';
     when "0000111100" | "0000111101" | "0000111110" |
          "0000111111" => IOM_POINTER <= "1111"; DATA_CLAMP <= '0';
     when others =>
       IOM_POINTER <= "0000";
       DATA_CLAMP <= '1';
   end case;
  if DATA_CLAMP = '0' then
    case IOM_POINTER is
    when "0000" =>
      DATA_IN <= IOMBITS(15);
    when "0001" =>
      DATA_IN <= IOMBITS(14);
    when "0010" =>
      DATA_IN <= IOMBITS(13);
    when "0011" =>
      DATA_IN <= IOMBITS(12);
    when "0100" =>
      DATA_IN <= IOMBITS(11);
    when "0101" =>
      DATA_IN <= IOMBITS(10);
    when "0110" =>
      DATA_IN <= IOMBITS(9);
    when "0111" =>
      DATA_IN <= IOMBITS(8);
    when "1000" =>
      DATA_IN <= IOMBITS(7);
    when "1001" =>
      DATA_IN <= IOMBITS(6);
    when "1010" =>
      DATA_IN <= IOMBITS(5) ;
    when "1011" =>
      DATA_IN <= IOMBITS(4) ;
    when "1100" =>
      DATA_IN <= IOMBITS(3) ;
    when "1101" =>
      DATA_IN <= IOMBITS(2) ;
    when "1110" =>
      DATA_IN <= IOMBITS(1) ;
    when "1111" =>
      DATA_IN <= IOMBITS(0) ;
    when others =>
      null;
    end case;
  else
    DATA_IN <= '1';
  end if;
end process;
-- GROUP ID STATE MACHINE 
GROUP_STATE_MACHINE: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      GROUP_ID_STATE <= SEARCH ;
    elsif VAR_RD3 = '0' then
      GROUP_ID_STATE <= IN_GROUP_ID_STATE;
    elsif OCTET_STROBE = '1' then
        if DATA_MODE = '1' and GROUP_ID_STATE = FROZEN then
          GROUP_ID_STATE <= FROZEN;
        elsif FAW_SYNC_FOUND = '1' then
          if IC_SYNC_FOUND = '1' then
            if IC_POSITION = '1' and GROUP_ID_POSITION = '1' then
              if GROUP_ID_MATCHED = '1' then
                case GROUP_ID_STATE is
                when SEARCH =>
                  GROUP_ID_STATE <= MATCH;
                when MATCH =>
                  GROUP_ID_STATE <= FOUND_TWICE;
                when FOUND_TWICE =>
                  GROUP_ID_STATE <= FROZEN;
                when FROZEN =>
                  GROUP_ID_STATE <= FROZEN;
                end case;
              else
                case GROUP_ID_STATE is
                when FROZEN =>
                  GROUP_ID_STATE <= FROZEN;
                when others =>
                  GROUP_ID_STATE <= SEARCH;
                end case;
              end if;
            end if;
          else
            GROUP_ID_STATE <= SEARCH;
          end if;
        else
          if IC_SYNC_FOUND = '1' then
            if GROUP_ID_POSITION = '1' then
              if GROUP_ID_MATCHED = '1' then
                case GROUP_ID_STATE is
                when SEARCH =>
                  GROUP_ID_STATE <= MATCH;
                when MATCH =>
                  GROUP_ID_STATE <= FOUND_TWICE;
                when FOUND_TWICE =>
                  GROUP_ID_STATE <= FROZEN;
                when FROZEN =>
                  GROUP_ID_STATE <= FROZEN;
                end case;
              else
                case GROUP_ID_STATE is
                when FROZEN =>
                  GROUP_ID_STATE <= FROZEN;
                when others =>
                  GROUP_ID_STATE <= SEARCH;
                end case;
              end if;
            end if;
          else
            GROUP_ID_STATE <= SEARCH;
          end if;
        end if ;
    end if;
    case GROUP_ID_STATE is
      when SEARCH | MATCH | FOUND_TWICE =>
        GROUP_ID_SYNC <= '0';
      when FROZEN =>
        GROUP_ID_SYNC <= '1';
    end case;
end process;
 
GROUP_ERROR_MACHINE: process
begin
  wait until RISING_EDGE (CLOCK);
    if RESET = '0' then
      GROUP_ERR <= NOERROR ;
    else
      case GROUP_ERR is
      when NOERROR =>
      if COMMON_RST = '0' then
        GROUP_ERR <= NOERROR;
      elsif OCTET_STROBE = '1' and GROUP_ERROR = '1' then
        GROUP_ERR <= ERRORA;
      else
        GROUP_ERR <= NOERROR;
      end if;
      when ERRORA =>
      if COMMON_RST = '0' then
        GROUP_ERR <= ERRORB;
      else
        GROUP_ERR <= ERRORA;
      end if;
      when ERRORB =>
      if COMMON_RST = '0' then
        GROUP_ERR <= NOERROR;
      elsif OCTET_STROBE = '1' and GROUP_ERROR = '1' then
        GROUP_ERR <= ERRORA;
      end if;
      end case;
    end if;
    if GROUP_ID_SYNC = '1' then
      if (GROUP_ID = GROUP_STORE) then
        GROUP_ERROR <= '0';
      else
        GROUP_ERROR <= '1';
      end if;
    else
      GROUP_ERROR <= '0';
    end if;
    case GROUP_ERR is
    when NOERROR =>
      GROUP_ID_ERROR <= '0';
    when ERRORA | ERRORB =>
      GROUP_ID_ERROR <= '1';
    end case;
end process;
 
-- GROUP ID STORE
-- Holds the value to the group
-- id calculated for the line.
GROUP_MACHINE: process
begin
  wait until RISING_EDGE (CLOCK);
    -- Test for Group ID in Register.
    if RESET = '0' then 
      GROUP_ID_MATCHED <= '0';
    elsif REGISTER_CONTENTS(6 downto 1) = GROUP_STORE then
      GROUP_ID_MATCHED <= '1';
    else
      GROUP_ID_MATCHED <= '0';
    end if;
 
    -- If the state machine has not found
    -- sync save the on-line value of group ID
    if RESET = '0' then
      GROUP_STORE <= "000000";
    elsif VAR_RD1 = '0' then
      GROUP_STORE <= VARIABLE_RESTORE(5 downto 0);
    elsif VAR_RD0 = '0' and GROUP_ID_SYNC = '0' then
      if FAW_SYNC_FOUND = '1' then
        if IC_SYNC_FOUND = '1' then
          if IC_POSITION = '1' and GROUP_ID_POSITION = '1' then
            GROUP_STORE <= REGISTER_CONTENTS(6 downto 1);
          else
            GROUP_STORE <= GROUP_STORE;
          end if;
        else
          GROUP_STORE <= "111111";
        end if;
      else
        if IC_SYNC_FOUND = '1' then
          if GROUP_ID_POSITION = '1' then
            GROUP_STORE <= REGISTER_CONTENTS(6 downto 1);
          else
            GROUP_STORE <= GROUP_STORE;
          end if;
        else
          GROUP_STORE <= "111111";
        end if;
      end if;
    else
      GROUP_STORE <= GROUP_STORE;
    end if;
end process;

-- Signal Assignments (internal)
VCOUNT            <= VCOUNTB & VCOUNTA;
DELAYED_COLUMN    <= DCOLUMN;
IN_IC_STATE       <= ULV2BIT_TO_FRAME_MAC_STATES(VARIABLE_RESTORE(1 downto 0));
IN_FAW_STATE      <= ULV3BIT_TO_MAC_STATES(VARIABLE_RESTORE(6 downto 4));
OCTET_COUNT       <= OCOUNTB & OCOUNTA ;
ICHAN_COUNT       <= ICOUNT;
STATES_ICHAN      <= FRAME_MAC_STATES_TO_ULV2BIT(ICHAN_STATE);
STATES_FAW        <= MAC_STATES_TO_ULV3BIT(FAW_STATE);
STATES_FRAME      <= FRAME_MAC_STATES_TO_ULV2BIT(FRAME_STATE);
STATES_CHAN_ID    <= PERSIST_MAC_STATES_TO_ULV2BIT(CHAN_ID_STATE);
STATES_CRC        <= CYC_STATE_TO_ULV2BIT(CRCSTATE);
STATES_GROUP      <= PERSIST_MAC_STATES_TO_ULV2BIT(GROUP_ID_STATE);
FRAMES            <= FRCOUNTB & FRCOUNTA;
IN_FRAME_STATE    <= ULV2BIT_TO_FRAME_MAC_STATES(VARIABLE_RESTORE(5 downto 4));
IN_CHAN_ID_STATE  <= ULV2BIT_TO_PERSIST_MAC_STATES(VARIABLE_RESTORE(1 downto 0));
IN_GROUP_ID_STATE <= ULV2BIT_TO_PERSIST_MAC_STATES(VARIABLE_RESTORE(7 downto 6));
IN_CRC_STATE      <= ULV2BIT_TO_CYC_STATE (VARIABLE_RESTORE(7 downto 6));
IOM_RESET         <= IOM_RETIME_ONE and IOM_RETIME_TWO ;


-- Signal Assignments (external)
VARIABLE_ADDRESS <= VARIABLE_COLUMN & VARIABLE_NUMBER;
FRAME_STORE_DATA(0) <= REGISTER_CONTENTS(7);
FRAME_STORE_DATA(1) <= REGISTER_CONTENTS(6);
FRAME_STORE_DATA(2) <= REGISTER_CONTENTS(5);
FRAME_STORE_DATA(3) <= REGISTER_CONTENTS(4);
FRAME_STORE_DATA(4) <= REGISTER_CONTENTS(3);
FRAME_STORE_DATA(5) <= REGISTER_CONTENTS(2);
ADDRESS_POINTER <= STORED_VALUE;
FS_ADDRESS <= FRAMES & OCTET_COUNT & CHANNEL_ID;
COMMON_RESET <= COMMON_RST;

end RTL ;



