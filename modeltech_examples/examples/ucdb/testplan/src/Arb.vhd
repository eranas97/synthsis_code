library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_ARITH.all;
use IEEE.STD_LOGIC_UNSIGNED.all;

entity ARBITRATOR is
  port (CLOCK: in STD_LOGIC;
        RESET: in STD_LOGIC;
        PRE_PROC_WR_REQUEST: in STD_LOGIC;
        POST_PROC_RD_REQUEST: in STD_LOGIC;
        CPU_WR: in STD_LOGIC;
        CPU_RD: in STD_LOGIC;
        MEMORY_CS: in STD_LOGIC;
        ADD_MUX_SEL: out STD_LOGIC;
        FRAME_STORE_OE: out STD_LOGIC;
        FRAME_STORE_WE: out STD_LOGIC;
        FRAME_STORE_STROBE: out STD_LOGIC;
        FRAME_STORE_CS: out STD_LOGIC;
        CPU_READY: out STD_LOGIC;
        CPU_FS_WE: out STD_LOGIC;
        CPU_FS_RD: out STD_LOGIC);
end;

architecture RTL of ARBITRATOR is
  type FS_STATE is (IDLE,PRE_PROC_WR1,PRE_PROC_WR2,POST_PROC_RD,
                    CPU_READ1,CPU_READ2,CPU_WR1,CPU_WR2);
  signal FRAME_STORE_STATE: FS_STATE;
  signal RDFLAG_KEEP: STD_LOGIC;
  signal WRFLAG_KEEP: STD_LOGIC;
  signal WRFLAG: STD_LOGIC;
  signal RDFLAG: STD_LOGIC;
  signal CPU_RD_DELAYED: STD_LOGIC;
  signal CPU_WR_DELAYED: STD_LOGIC;
  signal ADDRESS_MUX_SEL: STD_LOGIC;
  
  -- PSL default clock is rising_edge(CLOCK);
  
  -- PSL sequence WRITE_REG_SEQUENCE is
  --     {not PRE_PROC_WR_REQUEST ; [*1] ; not FRAME_STORE_WE };
  -- PSL Cover_Write_Reg_Check : cover WRITE_REG_SEQUENCE ;
  -- PSL sequence RD_REG_SEQUENCE is
  --     {not POST_PROC_RD_REQUEST ; not FRAME_STORE_OE };
  -- PSL Cover_Read_Reg_Check : cover RD_REG_SEQUENCE ;
  
  -- PSL sequence PRE_PROC_WRITE is
  --     {FRAME_STORE_STATE = IDLE ; FRAME_STORE_STATE = PRE_PROC_WR1 ; FRAME_STORE_STATE = PRE_PROC_WR2 ; FRAME_STORE_STATE = IDLE };
  -- PSL Cover_Pre_Proc_Write : cover PRE_PROC_WRITE ;
  -- PSL sequence POST_PROC_READ is
  --     {FRAME_STORE_STATE = IDLE ; FRAME_STORE_STATE = POST_PROC_RD ; FRAME_STORE_STATE = IDLE };
  -- PSL Cover_Post_Proc_Read : cover POST_PROC_READ ;
  -- PSL sequence CPU_WRITE is
  --     {FRAME_STORE_STATE = IDLE ; FRAME_STORE_STATE = CPU_WR1 ; FRAME_STORE_STATE = CPU_WR2 ; FRAME_STORE_STATE = IDLE };
  -- PSL Cover_CPU_Write : cover CPU_WRITE ;
  -- PSL sequence CPU_READ is
  --     {FRAME_STORE_STATE = IDLE ; FRAME_STORE_STATE = CPU_READ1 ; FRAME_STORE_STATE = CPU_READ2 ; FRAME_STORE_STATE = IDLE };
  -- PSL Cover_CPU_Read : cover CPU_READ ;
  -- PSL sequence PRE_POST_WR_INTS_CPU_READ is
  --     {FRAME_STORE_STATE = CPU_READ1 ; FRAME_STORE_STATE = PRE_PROC_WR1 ; FRAME_STORE_STATE = PRE_PROC_WR2 ; FRAME_STORE_STATE = CPU_READ1 };
  -- PSL Cover_Pre_Proc_Ints_CPU_Read : cover PRE_POST_WR_INTS_CPU_READ ;
  -- PSL sequence PRE_POST_WR_INTS_CPU_WRITE is
  --     {FRAME_STORE_STATE = CPU_WR1 ; FRAME_STORE_STATE = PRE_PROC_WR1 ; FRAME_STORE_STATE = PRE_PROC_WR2 ; FRAME_STORE_STATE = CPU_WR1 };
  -- PSL Cover_Pre_Proc_Ints_CPU_Write : cover PRE_POST_WR_INTS_CPU_WRITE ;
  -- PSL sequence POST_POST_RD_INTS_CPU_READ is
  --     {FRAME_STORE_STATE = CPU_READ1 ; FRAME_STORE_STATE = POST_PROC_RD ; FRAME_STORE_STATE = CPU_READ1 };
  -- PSL Cover_Post_Proc_Ints_CPU_Read : cover POST_POST_RD_INTS_CPU_READ ;
  -- PSL sequence POST_POST_RD_INTS_CPU_WRITE is
  --     {FRAME_STORE_STATE = CPU_WR1 ; FRAME_STORE_STATE = POST_PROC_RD ; FRAME_STORE_STATE = CPU_WR1 };
  -- PSL Cover_Post_Proc_Ints_CPU_Write : cover POST_POST_RD_INTS_CPU_WRITE ;

  
  -- PSL property WRITE_REG_CHECK is 
  --     {fell(PRE_PROC_WR_REQUEST) } |=> { [*1] ; not FRAME_STORE_WE } ;
  -- PSL Assert_Write_Reg_Check : assert always WRITE_REG_CHECK ;
  -- PSL property RD_REG_CHECK is 
  --     {fell(POST_PROC_RD_REQUEST) } |=> { not FRAME_STORE_OE } ;
  -- PSL Assert_Read_Reg_Check : assert always RD_REG_CHECK ;
  -- PSL property PRE_PROC_WRITE_CHECK is
  --     {FRAME_STORE_STATE = IDLE } |=> { FRAME_STORE_STATE = PRE_PROC_WR1 ; FRAME_STORE_STATE = PRE_PROC_WR2 ; FRAME_STORE_STATE = IDLE };
  -- PSL Assert_Pre_Proc_Write : assert always PRE_PROC_WRITE_CHECK ;
  
  -- PSL property POST_PROC_READ_CHECK is
  --     {FRAME_STORE_STATE = IDLE } |=> { FRAME_STORE_STATE = POST_PROC_RD ; FRAME_STORE_STATE = IDLE };
  -- PSL Assert_Post_Proc_Read : assert always POST_PROC_READ_CHECK ;
  -- PSL property CPU_WRITE_CHECK is
  --     {FRAME_STORE_STATE = IDLE } |=> { FRAME_STORE_STATE = CPU_WR1 ; FRAME_STORE_STATE = CPU_WR2 ; FRAME_STORE_STATE = IDLE };
  -- PSL Assert_CPU_Write : assert always CPU_WRITE_CHECK ;
  -- PSL property CPU_READ_CHECK is
  --     {FRAME_STORE_STATE = IDLE } |=> { FRAME_STORE_STATE = CPU_READ1 ; FRAME_STORE_STATE = CPU_READ2 ; FRAME_STORE_STATE = IDLE };
  -- PSL Assert_CPU_Read : assert always CPU_READ_CHECK ;
  -- PSL property PRE_POST_WR_INTS_CPU_READ_CHECK is
  --     {FRAME_STORE_STATE = CPU_READ1 } |=> { FRAME_STORE_STATE = PRE_PROC_WR1 ; FRAME_STORE_STATE = PRE_PROC_WR2 ; FRAME_STORE_STATE = CPU_READ1 };
  -- PSL Assert_Pre_Proc_Ints_CPU_Read : assert always PRE_POST_WR_INTS_CPU_READ_CHECK ;
  -- PSL property PRE_POST_WR_INTS_CPU_WRITE_CHECK is
  --     {FRAME_STORE_STATE = CPU_WR1 } |=> { FRAME_STORE_STATE = PRE_PROC_WR1 ; FRAME_STORE_STATE = PRE_PROC_WR2 ; FRAME_STORE_STATE = CPU_WR1 };
  -- PSL Assert_Pre_Proc_Ints_CPU_Write : assert always PRE_POST_WR_INTS_CPU_WRITE_CHECK ;
  -- PSL property POST_POST_RD_INTS_CPU_READ_CHECK is
  --     {FRAME_STORE_STATE = CPU_READ1 } |=> { FRAME_STORE_STATE = POST_PROC_RD ; FRAME_STORE_STATE = CPU_READ1 };
  -- PSL Assert_Post_Proc_Ints_CPU_Read : assert always POST_POST_RD_INTS_CPU_READ_CHECK ;
  -- PSL property POST_POST_RD_INTS_CPU_WRITE_CHECK is
  --     {FRAME_STORE_STATE = CPU_WR1 } |=> { FRAME_STORE_STATE = POST_PROC_RD ; FRAME_STORE_STATE = CPU_WR1 };
  -- PSL Assert_Post_Proc_Ints_CPU_Write : assert always POST_POST_RD_INTS_CPU_WRITE_CHECK ;


     
begin
STATE_MAC: process
  begin
    wait until RISING_EDGE (CLOCK);
      if RESET = '0' then
        FRAME_STORE_STATE      <= IDLE;
        ADDRESS_MUX_SEL        <= '0';
        FRAME_STORE_WE         <= '1';
        FRAME_STORE_OE         <= '1';
        RDFLAG_KEEP            <= '1';
        WRFLAG_KEEP            <= '1';
        FRAME_STORE_STROBE     <= '1';
        CPU_FS_WE              <= '1';
      else
        case FRAME_STORE_STATE is
        when IDLE =>
          if PRE_PROC_WR_REQUEST = '0' then
            FRAME_STORE_STATE <= PRE_PROC_WR1;
            ADDRESS_MUX_SEL <= '1';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          elsif POST_PROC_RD_REQUEST = '0' then
            FRAME_STORE_STATE <= POST_PROC_RD;
            ADDRESS_MUX_SEL <= '1';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '0';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          elsif WRFLAG = '1' then
            FRAME_STORE_STATE <= CPU_WR1;
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          elsif RDFLAG = '1' then
            FRAME_STORE_STATE <= CPU_READ1;
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          else
            FRAME_STORE_STATE <= IDLE;
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          end if;
        when PRE_PROC_WR1 =>
          FRAME_STORE_STATE <= PRE_PROC_WR2;
          ADDRESS_MUX_SEL <= '1';
          FRAME_STORE_WE  <= '0';
          FRAME_STORE_OE  <= '1';
          RDFLAG_KEEP     <= '1';
          WRFLAG_KEEP     <= '1';
          FRAME_STORE_STROBE     <= '1';
          CPU_FS_WE     <= '1';
        when PRE_PROC_WR2 =>
          if WRFLAG = '1' then
            FRAME_STORE_STATE <= CPU_WR1;
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          elsif RDFLAG = '1' then
            FRAME_STORE_STATE <= CPU_READ1;
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          else
            FRAME_STORE_STATE <= IDLE;
            ADDRESS_MUX_SEL <= '0'; 
            FRAME_STORE_WE  <= '1'; 
            FRAME_STORE_OE  <= '1'; 
            RDFLAG_KEEP     <= '1'; 
            WRFLAG_KEEP     <= '1'; 
            FRAME_STORE_STROBE     <= '1'; 
            CPU_FS_WE     <= '1';
          end if;
        when POST_PROC_RD =>
          if WRFLAG = '1' then
            FRAME_STORE_STATE <= CPU_WR1;
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          elsif RDFLAG = '1' then 
            FRAME_STORE_STATE <= CPU_READ1;
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          else  
            FRAME_STORE_STATE <= IDLE;
            ADDRESS_MUX_SEL <= '0';  
            FRAME_STORE_WE  <= '1';  
            FRAME_STORE_OE  <= '1';  
            RDFLAG_KEEP     <= '1';  
            WRFLAG_KEEP     <= '1';  
            FRAME_STORE_STROBE     <= '1';  
            CPU_FS_WE     <= '1';
          end if;
        when CPU_READ1 =>
          if PRE_PROC_WR_REQUEST = '0' then
            FRAME_STORE_STATE <= PRE_PROC_WR1;
            ADDRESS_MUX_SEL <= '1';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          elsif POST_PROC_RD_REQUEST = '0' then
            FRAME_STORE_STATE <= POST_PROC_RD;
            ADDRESS_MUX_SEL <= '1';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '0';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          else
            FRAME_STORE_STATE <= CPU_READ2;
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '0';
            RDFLAG_KEEP     <= '0';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '0';
            CPU_FS_WE     <= '1';
          end if; 
        when CPU_READ2 =>
          if PRE_PROC_WR_REQUEST = '0' then
            FRAME_STORE_STATE <= PRE_PROC_WR1;
            ADDRESS_MUX_SEL <= '1';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          elsif POST_PROC_RD_REQUEST = '0' then
            FRAME_STORE_STATE <= POST_PROC_RD;
            ADDRESS_MUX_SEL <= '1';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '0';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          else
            FRAME_STORE_STATE <= IDLE;
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          end if; 
        when CPU_WR1 =>
          if PRE_PROC_WR_REQUEST = '0' then 
            FRAME_STORE_STATE <= PRE_PROC_WR1; 
            ADDRESS_MUX_SEL <= '1';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          elsif POST_PROC_RD_REQUEST = '0' then 
            FRAME_STORE_STATE <= POST_PROC_RD; 
            ADDRESS_MUX_SEL <= '1';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '0';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          else 
            FRAME_STORE_STATE <= CPU_WR2;
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '0';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '0';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '0';
          end if;  
        when CPU_WR2 =>
          if PRE_PROC_WR_REQUEST = '0' then 
            FRAME_STORE_STATE <= PRE_PROC_WR1; 
            ADDRESS_MUX_SEL <= '1';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          elsif POST_PROC_RD_REQUEST = '0' then 
            FRAME_STORE_STATE <= POST_PROC_RD;  
            ADDRESS_MUX_SEL <= '1';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '0';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          else  
            FRAME_STORE_STATE <= IDLE; 
            ADDRESS_MUX_SEL <= '0';
            FRAME_STORE_WE  <= '1';
            FRAME_STORE_OE  <= '1';
            RDFLAG_KEEP     <= '1';
            WRFLAG_KEEP     <= '1';
            FRAME_STORE_STROBE     <= '1';
            CPU_FS_WE     <= '1';
          end if;   
        when others =>
          null;
        end case;
      end if;
  end process;

FLAG_GEN: process
  begin
    wait until RISING_EDGE (CLOCK);
      CPU_RD_DELAYED <= CPU_RD;
      if RESET = '0' or RDFLAG_KEEP = '0' then
        RDFLAG <= '0';
      elsif CPU_RD = '0' and CPU_RD_DELAYED = '1' and MEMORY_CS = '0' then
        RDFLAG <= '1';
      end if;
      CPU_WR_DELAYED <= CPU_WR;
      if RESET = '0' or WRFLAG_KEEP = '0' then
        WRFLAG <= '0';
      elsif CPU_WR = '0' and CPU_WR_DELAYED = '1' and MEMORY_CS = '0' then
        WRFLAG <= '1';
      end if;
  end process;

FRAME_STORE_CS <= ADDRESS_MUX_SEL nor (not(ADDRESS_MUX_SEL) and (CPU_RD nand CPU_WR) and not(MEMORY_CS));
CPU_READY <= not((RDFLAG_KEEP and RDFLAG) or (WRFLAG_KEEP and WRFLAG)) ;
CPU_FS_RD <= CPU_RD or MEMORY_CS ;
ADD_MUX_SEL <= ADDRESS_MUX_SEL;

end RTL;
