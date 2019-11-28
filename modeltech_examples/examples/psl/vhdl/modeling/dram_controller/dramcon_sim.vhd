
library IEEE;
  use IEEE.std_logic_1164.all;
  use IEEE.numeric_std.all;
  use IEEE.std_logic_textio.all;
  use WORK.constants.all;
  use STD.textio.all;
entity tb is
end entity tb;

architecture behav of tb is

  constant DEL          : Time := 1 ns; -- Clock-to-output delay. Zero
                                        -- time delays can be confusing
                                        -- and sometimes cause problems.
  constant DEL2         : Time := 2 ns; -- Longer clock-to-output delay.
  constant ACC_COUNT    : Natural := 4; -- Maximum number of cycles needed
                                        -- to access memory
  constant CLK_HPERIOD : Time := 50 ns; -- Clock half period
                                        -- Clock period
  constant CLK_PERIOD  : Time := CLK_HPERIOD*2; 
  constant WR_PERIOD   : Time := 70 ns; -- Write access time of memory
                                        -- from assertion of CAS
  constant RD_PERIOD   : Time := 120 ns;-- Read access time of memory
                                        -- from assertion of CAS
  constant DWIDTH      : Natural := 8;  -- Data width of DRAM
  constant DDEPTH      : Natural := 256;-- Data depth of DRAM

  signal clk         : std_logic := '1';
  signal reset       : std_logic := '0';
  signal addr_in       : std_logic_vector(AIN-1 downto 0);
  signal as            : std_logic := '1';
  signal rw            : std_logic;
  signal we_n          : std_logic;
  signal ras_n         : std_logic;
  signal cas_n         : std_logic;
  signal ack           : std_logic;
  signal addr_out      : std_logic_vector(AOUT-1 downto 0);
  signal err_cnt       : Natural := 0;
  signal data_out      : std_logic_vector(DWIDTH-1 downto 0);
                                     -- Data out of processor
  signal data          : std_logic_vector(DWIDTH-1 downto 0); -- Data bus
  signal cyc_count     : Natural := 0;  -- Count cycles to determine
                                        -- if the access has taken
                                        -- too long
  signal stop          : boolean := false;

  -- Write data to memory
  procedure writemem(
           write_addr : IN    UNSIGNED(AIN-1 downto 0);
           write_data : IN    UNSIGNED(DWIDTH-1 downto 0);
    signal cyc_count  : INOUT Natural;
    signal rw         : OUT   std_logic;
    signal addr_in    : OUT   std_logic_vector(AIN-1 downto 0);
    signal data_out   : OUT   std_logic_vector(DWIDTH-1 downto 0);
    signal as         : OUT   std_logic )
  is
  begin

    cyc_count <= 0;                   -- Initialize the cycle count

    -- Wait for the rising clock edge
    wait until rising_edge(clk);
    wait for 1 ns;
    rw <= '0';                        -- Set up a write access
                                      -- Set up the address
    addr_in <= std_logic_vector(write_addr);
    
    -- Set up the data to be written
    data_out <= std_logic_vector(write_data);

    wait for 1 ns;
    as <= '1';                      -- Assert address strobe

    -- Wait for the acknowledge
    wait until rising_edge(clk);

    while (ack = '0') loop
      -- Increment the cycle count
      cyc_count <= cyc_count + 1;

      wait until rising_edge(clk);
    end loop;

    wait for 1 ns;
    as <= '0';                          -- Deassert address strobe
    wait until rising_edge(clk);      -- Wait one clock cycle

  end procedure writemem;

  -- Read data from memory and check its value
  procedure readmem(
            read_addr : IN    UNSIGNED((AIN-1) downto 0);
            exp_data  : IN    UNSIGNED((DWIDTH-1) downto 0);
     signal cyc_count : INOUT Natural;
     signal rw        : OUT   std_logic;
     signal addr_in   : OUT   std_logic_vector(AIN-1 downto 0);
     signal as        : OUT   std_logic )
  is
     variable l : line;
     variable local_exp_data : std_logic_vector((DWIDTH-1) downto 0) :=
               std_logic_vector(exp_data);
  begin

    cyc_count <= 0;               -- Initialize the cycle count

    -- Wait for the rising clock edge
    wait until rising_edge(clk);
    wait for 1 ns;
    rw <= '1';                    -- Set up a read access
                                  -- Set up the address
    addr_in <= std_logic_vector(read_addr);
    wait for 1 ns;
    as <= '1';                    -- Assert address strobe

    -- Wait for the acknowledge
    wait until rising_edge(clk);
    while (ack = '0') loop
      -- Increment the cycle count
      cyc_count <= cyc_count + 1;

      wait until rising_edge(clk);
    end loop;

    -- Did we find the expected data?
    if (data /= local_exp_data) then
      write(l, string'("Controller is not working"));
      writeline(OUTPUT, l);
      write(l, string'("    data written = "));
      write(l, local_exp_data);
      writeline(OUTPUT, l);
      write(l, string'("    data read    = "));
      write(l, data);
      writeline(OUTPUT, l);
      report "ERROR at time " & time'image(now) severity FAILURE;
    end if;

    wait for 1 ns;
    as <= '0';                      -- Deassert address strobe
    wait until rising_edge(clk);  -- Wait one clock cycle

  end procedure readmem;

begin

  data <= (others => 'Z') when (as = '1') and (we_n = '1') else data_out;

  -- Instantiate the controller
  cntrl : entity work.dram_control
           port map (
                clk      => clk,
                reset_n  => "not"(reset),
                as_n     => "not"(as),
                addr_in  => addr_in,
                addr_out => addr_out,
                rw       => rw,
                we_n     => we_n,
                ras_n    => ras_n,
                cas_n    => cas_n,
                ack      => ack );

  -- Instantiate a DRAM
  RAM : entity work.DRAM
         generic map (AOUT, DWIDTH, AIN, DDEPTH, RD_PERIOD, WR_PERIOD)
         port map (
                ras     => "not"(ras_n),
		cas     => "not"(cas_n),
		we      => "not"(we_n),
		address => addr_out,
		data    => data  );

  -- Generate the clock
  process
  begin
    if stop then
      wait;
    end if;
    clk <= not clk after CLK_HPERIOD;
    wait on clk;
  end process;

  -- stimulus generator / response checker
  main: process
    variable l : line;
    variable data_patt : UNSIGNED(DWIDTH-1 downto 0);           -- Data pattern holder
    variable addr_count: UNSIGNED(AIN downto 0) := (others => '0'); -- Address counter
  begin
    wait for 1 ns;
    wait for 4 * CLK_HPERIOD;
    reset <= '1';

    -- Check to ensure design is reset properly
    wait for 2 ns;
	wait until rising_edge(clk);
    if ((ras_n = '1') and (cas_n = '1') and (ack = '0')) then
      report "Reset is working" severity NOTE;
    else
      write(l, string'("ERROR at time "));
      write(l, now);
      writeline(OUTPUT, l);
      write(l, string'("Reset is not working"));
      writeline(OUTPUT, l);
      write(l, string'("    ras_n = "));
      write(l, ras_n);
      writeline(OUTPUT, l);
      write(l, string'("    cas_n = "));
      write(l, cas_n);
      writeline(OUTPUT, l);
      write(l, string'("    ack   = "));
      write(l, ack);
      writeline(OUTPUT, l);
      assert FALSE report "Stopping simulation" severity FAILURE;
    end if;

    -- deassert reset
    reset <= '0';

    -- Initialize the data pattern to be written
    data_patt := "00010001";

    -- Write a series of values to memory
    while (addr_count(AIN) = '0') loop
      -- Write to memory
      writemem(addr_count((AIN-1) downto 0),
               data_patt,
               cyc_count,
               rw,
               addr_in,
               data_out,
               as );

      -- Increment the address counter
      addr_count := addr_count + 1;

      -- Rotate the data pattern
      data_patt := rotate_left(data_patt, 1);

    end loop;

    -- Initialize the address counter
    addr_count := (others => '0');

    -- Initialize the data pattern to be read
    data_patt := "00010001";

    -- Verify the values that were written	
    while (addr_count(AIN) = '0') loop
      -- Read from memory
      readmem(addr_count((AIN-1) downto 0),
              data_patt,
              cyc_count,
              rw,
              addr_in,
              as );

      -- Increment the address counter
      addr_count := addr_count + 1;

      -- Shift the data pattern
      data_patt := rotate_left(data_patt, 1);

    end loop;

    if err_cnt = 0 then
      report "Simulation complete - no errors"
        severity FAILURE;
    else
      report "Simulation finished with " & integer'image(err_cnt) & " errors!"
        severity FAILURE;
    end if;
    stop <= true;
    wait;
  end process;

  -- Check the number of cycles for each access
  process(clk)
  begin
    if rising_edge(clk) then
      -- Check whether an access is taking too long
      if (cyc_count > 3*ACC_COUNT) then
        err_cnt <= err_cnt + 1;
        if (rw = '1') then
          report "ERROR at time " & time'image(now) & " Read access took too long."
             severity FAILURE;
        else
          report "ERROR at time " & time'image(now) & " Write access took too long."
             severity FAILURE;
        end if;
      end if;
    end if;
  end process;

end architecture behav;
