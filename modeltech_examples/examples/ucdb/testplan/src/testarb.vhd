entity arb_tester is

end;

library IEEE;
use IEEE.STD_LOGIC_1164.all;
use IEEE.STD_LOGIC_UNSIGNED.all;
use IEEE.STD_LOGIC_ARITH.all;

architecture test of arb_tester is

component ARBITRATOR
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
end component;

signal CLK: STD_LOGIC := '1';
signal RST: STD_LOGIC := '1';
signal PRE_PROC_WR_REQUEST: STD_LOGIC := '1';
signal POST_PROC_RD_REQUEST: STD_LOGIC := '1';
signal CPU_WR: STD_LOGIC := '1';
signal CPU_RD: STD_LOGIC := '1';
signal MEMORY_CS: STD_LOGIC := '1';
signal ADD_MUX_SEL: STD_LOGIC := '1';
signal FRAME_STORE_OE: STD_LOGIC := '1';
signal FRAME_STORE_WE: STD_LOGIC := '1';
signal FRAME_STORE_STROBE: STD_LOGIC := '1';
signal FRAME_STORE_CS: STD_LOGIC := '1';
signal CPU_READY: STD_LOGIC := '1';
signal CPU_FS_WE: STD_LOGIC := '1';
signal CPU_FS_RD: STD_LOGIC := '1';

begin
    
CLK <= not (CLK) after 61 ns;

sim_runtime :process
begin
    PRE_PROC_WR_REQUEST <= '1';
    POST_PROC_RD_REQUEST <= '1';
    CPU_WR <= '1';
    CPU_RD <= '1';
    MEMORY_CS <= '1';
    RST <= '0';
    wait for (122 ns * 5) + 1 ns;
    -- A Pre-proc write
    RST <= '1';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '0';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '1';
    wait for 122 ns * 5;
    -- A Post-proc read
    POST_PROC_RD_REQUEST <=  '0';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '1';
    wait for 122 ns * 5;
    -- A Processor write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_WR <=  '0';
    wait for 122 ns;
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_WR <=  '1';
    wait for 122 ns * 5;
    -- A Processor Read
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';
    wait for 122 ns;
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_RD <=  '1';
    wait for 122 ns * 5;
    -- A Processor write During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_WR <=  '0';
    PRE_PROC_WR_REQUEST <=  '0';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '1';
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_WR <=  '1';
    wait for 122 ns * 5;
    -- A Processor write During Post-Proc read
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_WR <=  '0';
    POST_PROC_RD_REQUEST <=  '0';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '1';
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_WR <=  '1';
    wait for 122 ns * 5;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';
    PRE_PROC_WR_REQUEST <=  '0';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '1';
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_RD <=  '1';
    wait for 122 ns * 5;
    -- A Processor write During Post-Proc read
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';
    POST_PROC_RD_REQUEST <=  '0';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '1';
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_RD <=  '1';
    wait for 122 ns * 5;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';  
    wait for 122 ns;
    MEMORY_CS <=  '1';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '0';
    CPU_RD <=  '1';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '1';
    wait for 122 ns * 4;
    -- A Processor write During Post-Proc read
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_WR <=  '0';  
    wait for 122 ns;
    MEMORY_CS <=  '1';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '0';
    CPU_WR <=  '1';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '1';
    wait for 122 ns * 4;
    -- A Processor Read During Post-Proc read
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';
    POST_PROC_RD_REQUEST <=  '0';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '1';
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_RD <=  '1';
    wait for 122 ns * 5;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';
    PRE_PROC_WR_REQUEST <=  '0';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '1';
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_RD <=  '1';
    wait for 122 ns * 5;
    -- A Processor Write During Post-Proc read
    MEMORY_CS <=  '0';
    wait for 122 ns;    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';  
    wait for 122 ns;
    MEMORY_CS <=  '1';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '0';
    CPU_RD <=  '1';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '1';
    wait for 122 ns * 4;
    CPU_WR <=  '0';
    POST_PROC_RD_REQUEST <=  '0';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '1';
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_WR <=  '1';
    wait for 122 ns * 5;
    -- A Processor Write During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_WR <=  '0';
    PRE_PROC_WR_REQUEST <=  '0';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '1';
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_WR <=  '1';
    wait for 122 ns * 5;
    -- A Processor Read During Post-Proc read
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';
    POST_PROC_RD_REQUEST <=  '0';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '1';
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_RD <=  '1';
    wait for 122 ns * 5;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';  
    wait for 122 ns;
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_RD <=  '1';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '0';
    wait for 122 ns * 2;
    PRE_PROC_WR_REQUEST <=  '1';
    wait for 122 ns * 2;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_WR <=  '0';  
    wait for 122 ns;
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_WR <=  '1';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '0';
    wait for 122 ns * 2;
    PRE_PROC_WR_REQUEST <=  '1';
    wait for 122 ns * 2;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';  
    wait for 122 ns;
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_RD <=  '1';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '0';
    wait for 122 ns * 2;
    POST_PROC_RD_REQUEST <=  '1';
    wait for 122 ns * 2;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_WR <=  '0';  
    wait for 122 ns;
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_WR <=  '1';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '0';
    wait for 122 ns * 2;
    POST_PROC_RD_REQUEST <=  '1';
    wait for 122 ns * 2;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';
    wait for 122 ns;    
    MEMORY_CS <=  '1';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '0'; 
    CPU_RD <=  '1';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '1';
    wait for 122 ns * 5;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_WR <=  '0';
    wait for 122 ns;    
    MEMORY_CS <=  '1';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '0'; 
    CPU_WR <=  '1';
    wait for 122 ns;
    POST_PROC_RD_REQUEST <=  '1';
    wait for 122 ns * 5;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_WR <=  '0';
    wait for 122 ns;    
    MEMORY_CS <=  '1';
    wait for 122 ns;
    RST <=  '0'; 
    CPU_WR <=  '1';
    wait for 122 ns;
    RST <=  '1';
    wait for 122 ns * 5;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_RD <=  '0';
    wait for 122 ns;    
    MEMORY_CS <=  '1';
    wait for 122 ns;
    RST <=  '0'; 
    CPU_RD <=  '1';
    wait for 122 ns;
    RST <=  '1';
    wait for 122 ns * 5;
    -- A Processor Read During Pre-proc write
    MEMORY_CS <=  '0';
    wait for 122 ns;
    CPU_WR <=  '0';  
    wait for 122 ns;
    MEMORY_CS <=  '1';
    wait for 122 ns;
    CPU_WR <=  '1';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '0';
    wait for 122 ns;
    RST <= '0';
    wait for 122 ns;
    PRE_PROC_WR_REQUEST <=  '1';
    wait for 122 ns * 2; 
  assert false report "Simulation Finished" severity failure;
  wait;
end process sim_runtime;

ARB: ARBITRATOR
   port map (CLOCK => CLK,
             RESET => RST,
             PRE_PROC_WR_REQUEST => PRE_PROC_WR_REQUEST,
             POST_PROC_RD_REQUEST => POST_PROC_RD_REQUEST,
             CPU_WR => CPU_WR,
             CPU_RD => CPU_RD,
             MEMORY_CS => MEMORY_CS,
             ADD_MUX_SEL => ADD_MUX_SEL,
             FRAME_STORE_OE => FRAME_STORE_OE,
             FRAME_STORE_WE => FRAME_STORE_WE,
             FRAME_STORE_STROBE => FRAME_STORE_STROBE,
             FRAME_STORE_CS => FRAME_STORE_CS,
             CPU_READY => CPU_READY,
             CPU_FS_WE => CPU_FS_WE,
             CPU_FS_RD => CPU_FS_RD );

end test ;