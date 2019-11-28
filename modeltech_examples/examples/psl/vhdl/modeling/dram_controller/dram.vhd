library IEEE;
  use IEEE.std_logic_1164.all;
entity dram is
  generic ( AOUT : Natural := 4;
            DWIDTH : Natural := 8;
            AIN    : NATURAL := 8;
            DDEPTH : NATURAL := 256;
            RD_PERIOD : TIME := 120 ns;
            WR_PERIOD : TIME := 70 ns );
  port (
            ras     : IN    std_logic;
            cas     : IN    std_logic;
            we      : IN    std_logic;
            address : IN    std_logic_vector(AOUT-1 downto 0);
            data    : INOUT std_logic_vector(DWIDTH-1 downto 0));
end entity DRAM;

library IEEE;
  use IEEE.numeric_std.all;
architecture RTL of DRAM is

  subtype word is std_logic_vector(DWIDTH-1 downto 0);
  type mem_arr is array(DDEPTH-1 downto 0) of word;
  signal mem : mem_arr;
  signal mem_addr : std_logic_vector(AIN-1 downto 0);
  signal rd_time  : TIME := 0 ns;
  signal rd_dtime : TIME;         -- Time of the most recent change of
                                  -- the rd input
  signal wr_time  : TIME := 0 ns;
  signal wr_dtime : TIME;         -- Time of the most recent change of
                                  -- the wr input

  signal oen : std_logic := '0';  -- Internal output enable - this
                                  -- signal is asserted after the
                                  -- minimum CAS time for a read
  signal wen : std_logic := '0';  -- Internal write enable - this
                                  -- signal is asserted after the
                                  -- minimum CAS time for a write

begin

  wr_dtime <= wr_time after WR_PERIOD;
  rd_dtime <= rd_time after RD_PERIOD;

  -- Output the data if the we signal is high and the oe is
  -- asserted, which means that we met the minimum CAS time
  -- for a read
  data <= mem(to_integer(unsigned(address))) when (oen = '1') and (we = '0') else
          (others => 'Z');

  -- MAIN CODE

  -- Look for the RAS rising edge for the row address
  process(ras)
  begin
    if rising_edge(ras) then
      mem_addr(AIN-1 downto AOUT) <= address;
    end if;
  end process;

  process(cas)
  begin
    if rising_edge(cas) then             -- Look for CAS to start
      mem_addr(AOUT-1 downto 0) <= address;
      if we = '1' then
        wen <= '0', '1' after WR_PERIOD;
        -- This is a write
        -- If this is true, the last rising edge of CAS
        -- was exactly WR_PERIOD time units ago, so
        -- assert the internal write enable
        wen <= '1';
      else
        oen <= '0', '1' after RD_PERIOD;
      end if;
    elsif falling_edge(cas) then       -- Look for end of the access
      if (wen = '1') and (we = '1') then
        -- Write the data if the write enable is asserted
        -- which means we met the minimum wr pulse time
        mem(to_integer(unsigned(mem_addr))) <= data;
      end if;
      wen <= '0';      -- Turn off the internal write enable
      oen <= '0';      -- Turn off the internal output enable
    end if;
  end process;

end architecture RTL;
