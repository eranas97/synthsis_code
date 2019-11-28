package CONSTANTS is
  subtype count_range is Natural range 0 to 2;
  constant RBC_CYC : Count_Range := 2; -- Number of cycles to assert RAS before CAS
  constant CBR_CYC : Count_Range := 1; -- Number of cycles to assert CAS before RAS
  constant RACW_CYC: Count_Range := 1; -- Number of cycles to assert RAS and CAS
                                       -- together on a write
  constant RACR_CYC: Count_Range := 2; -- Number of cycles to assert RAS
                                       -- and CAS together for a read
  constant RACRF_CYC: Count_Range := 1;-- Number of cycles to assert RAS
                                       -- and CAS together for a refresh
  constant CNT_BITS: Count_Range := 2; -- Number of bits needed for the
                                       -- counter to count the cycles
                                       -- listed above
  constant REF_BITS: Natural := 5; -- Number of bits needed for the
                                   -- counter to count the cycles
                                   -- for a refresh
  -- Number of cycles between refreshes
  subtype REF_CNT_RANGE is Natural range 0 to 24;
  constant REF_CNT : Ref_Cnt_Range := 24;
  constant AOUT    : Natural := 4; -- Address bit width to DRAM
  constant AIN     : Natural := 2*AOUT; -- Address bit width from processor
end package constants;

library IEEE;
  use IEEE.std_logic_1164.all;
  use IEEE.numeric_std.all;
  use WORK.constants.all;
entity dram_control is
  generic ( BUG : Boolean := TRUE );
--  generic ( BUG : Boolean := FALSE );
  port ( clk     : IN     std_logic;
         reset_n : IN     std_logic;
         as_n    : IN     std_logic;
         addr_in : IN     std_logic_vector(AIN-1 downto 0);
         addr_out: OUT    std_logic_vector(AOUT-1 downto 0);
         rw      : IN     std_logic;  -- 1 to read; 0 to write
         we_n    : BUFFER    std_logic;
         ras_n   : BUFFER    std_logic;
         cas_n   : BUFFER    std_logic;
         ack     : OUT    std_logic );
end entity dram_control;

architecture RTL of dram_control is

  type memory_state is (IDLE, MEM_ACCESS, SWITCH, RAS_CAS, OP_ACK, REF1, REF2);
  signal mem_state : memory_state := IDLE;

  signal col_out   : std_logic; -- Output column address
                                -- = 1 for column address
                                -- = 0 for row address

  signal count     : natural range 0 to 2;        -- Cycle counter
  signal ref_count : natural range 0 to REF_CNT;  -- Refresh counter
  signal refresh   : std_logic;                   -- Refresh request

begin


  -- Deassert we_n high during refresh
  withbug : if BUG generate
    we_n <= '1' when (rw = '1') or (mem_state = REF1) else '0';
  end generate;

  nobug : if not BUG generate
    we_n <= '1' when (rw = '1') or (mem_state = REF1) or (mem_state = REF2) else '0';
  end generate;

  -- Give the row address or column address to the DRAM
  addr_out <= addr_in(AOUT-1 downto 0) when (col_out = '1') else
              addr_in(AIN-1 downto AOUT);

  -- Look at the rising edge of clk for state transitions
  process(clk, reset_n)
  begin
    if (reset_n = '0') then
      mem_state <= IDLE;
      count <= 0;
      ref_count <= REF_CNT;
      refresh   <= '0';

      -- Initialize outputs
      col_out <= '0';
      ras_n   <= '1';
      cas_n   <= '1';
      ack     <= '0';

    elsif rising_edge(clk) then
      -- Initialize outputs
      col_out <= '0';
      ras_n   <= '1';
      cas_n   <= '1';
      ack     <= '0';

      -- Time for a refresh request?
      if (ref_count = 0) then
        refresh <= '1';
        ref_count <= REF_CNT;
      else
        ref_count <= ref_count - 1;
      end if;

      -- Decrement cycle counter to zero
      if (count > 0) then
        count <= count - 1;
      end if;

      -- The FSM
      case (mem_state) is
        when IDLE =>
          -- Refresh request has highest priority
          if (refresh = '1') then
            -- Load the counter to assert CAS
            count <= CBR_CYC;
            mem_state <= REF1;
            cas_n <= '0';
          elsif (as_n = '0') then
            -- Load the counter to assert RAS
            count <= RBC_CYC;
            mem_state <= MEM_ACCESS;
            ras_n <= '0';
          end if;
          
        when MEM_ACCESS =>
          mem_state <= SWITCH;
          ras_n     <= '0';
          col_out   <= '1';
         
        when SWITCH =>
          ras_n     <= '0';
          col_out   <= '1';
          if (count = 0) then
			cas_n     <= '0';
            mem_state <= RAS_CAS;
            if (rw = '1') then
              count <= RACR_CYC;
            else
              count <= RACW_CYC;
            end if;
          end if;
          
        when RAS_CAS =>
          col_out <= '1';
          ras_n   <= '0';
          cas_n   <= '0';
          ack     <= '1';
         if (count = 0) then
            mem_state <= OP_ACK;
         end if;
          
        when OP_ACK =>
          mem_state <= IDLE;
          
        when REF1 =>
           cas_n <= '0';
           if (count = 0) then
             mem_state <= REF2;
             ras_n <= '0';
             count <= RACRF_CYC;
           end if;
          
        when REF2 =>
          refresh <= '0';
          if (count = 0) then
            mem_state <= IDLE;
          else 
            cas_n <= '0';
            ras_n <= '0';
          end if;
      end case;
    end if;
  end process;

end architecture RTL;
