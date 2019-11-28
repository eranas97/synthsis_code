library ieee;
    use ieee.std_logic_1164.all;
    use ieee.std_logic_unsigned.all;
library work;
    use work.all;


architecture RTL of interleaver_m0 is

  signal push      : std_logic_vector(10 downto 0);
  type fsm_state is(idle,send_bypass,load0,send0,load1,send1,
                    load2,send2,load3,send3,load4,send4,load5,
                    send5,load6,send6,load7,send7,load8,send8,
                    load9,send9,load10,send10,load_bypass,
                    wait_idle);
  signal int_state : fsm_state;
  signal nxt_state : fsm_state;
  signal in_hs     : std_logic;
  signal out_hs    : std_logic;
  signal in_acpt   : std_logic;
  signal out_acpt  : std_logic;
  signal out_rdy   : std_logic;
  signal in_rdy    : std_logic;
  signal pkt_cen   : std_logic;
  signal pkt_zero  : std_logic;
  signal pkt_ld_n  : std_logic;
  signal ram_re    : std_logic;
  signal do_reg    : std_logic_vector(7 downto 0);
  signal fifo_data : std_logic_vector(7 downto 0);
  signal data_sel  : std_logic_vector(3 downto 0);
  signal pkt_cnt   : std_logic_vector(7 downto 0);
  signal output_down_data : std_logic_vector(7 downto 0);
  signal input_down_data  : std_logic_vector(7 downto 0);
  signal cnt_din  : std_logic_vector(7 downto 0) :=X"CB";
  signal int_state_idle : std_logic;

-- default clock
-- psl default clock is rising_edge(clk);

-- Possible sync byte received
-- psl sequence sync_in_valid is {input_down_data = "01000111" OR input_down_data = "10111000"};

-- Check for sync byte at the start of a every packet
-- psl property pkt_start_check is always {(int_state = idle AND in_hs = '1')} |-> {sync_in_valid};
-- psl assert pkt_start_check;

-- Check that every packet is 204 bytes long
-- psl property pkt_length_check is always {int_state = idle AND in_hs = '1'} |->
--   {sync_in_valid; (in_hs = '1' AND int_state /= idle)[=203]};
-- psl assert pkt_length_check;

-- Check for sync byte being bypassed
-- psl property sync_bypass_check is always {in_hs = '1' AND int_state = idle AND
--   (input_down_data ="01000111" OR input_down_data = "10111000")} |=>
--   {(int_state = send_bypass AND out_hs = '1' AND (do_reg = "01000111" OR do_reg = "10111000"))[=1]};
-- psl assert sync_bypass_check;

-- psl sequence s_interleave_sm is {
-- rose((int_state = idle OR int_state = load_bypass) AND in_hs = '1'); (int_state = send_bypass and out_hs = '1')[->];
-- (int_state = load0  AND in_hs = '1')[->]; (int_state = send0  AND out_hs = '1')[->];
-- (int_state = load1  AND in_hs = '1')[->]; (int_state = send1  AND out_hs = '1')[->];
-- (int_state = load2  AND in_hs = '1')[->]; (int_state = send2  AND out_hs = '1')[->];
-- (int_state = load3  AND in_hs = '1')[->]; (int_state = send3  AND out_hs = '1')[->];
-- (int_state = load4  AND in_hs = '1')[->]; (int_state = send4  AND out_hs = '1')[->];
-- (int_state = load5  AND in_hs = '1')[->]; (int_state = send5  AND out_hs = '1')[->];
-- (int_state = load6  AND in_hs = '1')[->]; (int_state = send6  AND out_hs = '1')[->];
-- (int_state = load7  AND in_hs = '1')[->]; (int_state = send7  AND out_hs = '1')[->];
-- (int_state = load8  AND in_hs = '1')[->]; (int_state = send8  AND out_hs = '1')[->];
-- (int_state = load9  AND in_hs = '1')[->]; (int_state = send9  AND out_hs = '1')[->];
-- (int_state = load10 AND in_hs = '1')[->]; (int_state = send10 AND out_hs = '1')[->]};

-- psl c_interleave_sm : cover s_interleave_sm;

begin 

  int_state_idle <= '1' when int_state = idle else '0';
  in_hs     <= in_acpt AND in_rdy;
  out_hs    <= out_acpt AND out_rdy;
  in_acpt   <= '1' when int_state = idle OR
                        int_state = load_bypass OR 
                        int_state = load0   OR
                        int_state = load1  OR
                        int_state = load2  OR
                        int_state = load3  OR
                        int_state = load4  OR
                        int_state = load5  OR
                        int_state = load6  OR
                        int_state = load7  OR
                        int_state = load8  OR
                        int_state = load9  OR
                        int_state = load10 else
               '0';

  out_rdy   <= '1' when int_state = send_bypass OR
                        int_state = send0   OR
                        int_state = send1  OR
                        int_state = send2  OR
                        int_state = send3  OR
                        int_state = send4  OR
                        int_state = send5  OR
                        int_state = send6  OR
                        int_state = send7  OR
                        int_state = send8  OR
                        int_state = send9  OR
                        int_state = send10 else
               '0';
                   

  pkt_cen   <=  '1' when (reset_n = '1' AND in_hs = '1' AND
                          pkt_zero = '0') else '0';
  pkt_ld_n  <= '0' when int_state = idle else
                '1';

  data_sel <= "0001" when int_state = load1 OR int_state = send0  else
              "0010" when int_state = load2 OR int_state = send1  else
              "0011" when int_state = load3 OR int_state = send2  else
              "0100" when int_state = load4 OR int_state = send3  else
              "0101" when int_state = load5 OR int_state = send4  else
              "0110" when int_state = load6 OR int_state = send5  else
              "0111" when int_state = load7 OR int_state = send6  else
              "1000" when int_state = load8 OR int_state = send7  else
              "1001" when int_state = load9 OR int_state = send8  else
              "1010" when int_state = load10 OR int_state = send9 else
              "0000";

  ram_re   <= '1' when (out_hs = '1' AND
                       (int_state = send0  OR int_state = send1 OR
                        int_state = send2  OR int_state = send3 OR
                        int_state = send4  OR int_state = send5 OR
                        int_state = send6  OR int_state = send7 OR
                        int_state = send8  OR int_state = send9 OR
                        int_state = send10 or int_state = send_bypass)) else
               '0';

  process(clk)
  begin
  if(rising_edge(clk)) then
    if(in_hs = '1' AND (int_state = idle OR int_state = load_bypass)) then
      do_reg <= input_down_data;
    elsif(push /= "00000000000") then
      do_reg <= fifo_data;
    else
      do_reg <= do_reg;
    end if;
  end if;
  end process;
       
  process(clk,reset_n)
  begin
    if(reset_n = '0') then
      int_state <= idle;
    else
      if(rising_edge(clk)) then
        int_state <= nxt_state;
      end if; 
    end if; 
  end process;

  process(in_hs,int_state,pkt_zero,enable,out_hs)
  begin
     nxt_state   <= int_state;
     push        <= "00000000000";
     case int_state is
     when idle =>
       push   <= "00000000000";
       if(in_hs = '1') then
         nxt_state   <= send_bypass;
       else
         nxt_state   <= idle;
       end if;
     when send_bypass =>
      if(out_hs = '1') then
        if(enable = '1') then
          nxt_state   <= load0;
        else
          nxt_state   <= idle;
        end if;
      end if;
     when load0 =>
       if(in_hs = '1') then
         nxt_state   <= send0;
         push        <= "00000000001";
       end if;
     when send0 =>
      if(out_hs = '1') then
        nxt_state   <= load1;
      end if;
     when load1 =>
       if(in_hs = '1') then
         nxt_state   <= send1;
         push        <= "00000000010";
       end if;
     when send1 =>
      if(out_hs = '1') then
        nxt_state   <= load2;
      end if;
     when load2 =>
       if(in_hs = '1') then
         nxt_state   <= send2;
         push        <= "00000000100";
       end if;
     when send2 =>
      if(out_hs = '1') then
        nxt_state   <= load3;
      end if;
     when load3 =>
       if(in_hs = '1') then
         nxt_state   <= send3;
         push        <= "00000001000";
       end if;
     when send3 =>
      if(out_hs = '1') then
        nxt_state   <= load4;
      end if;
     when load4 =>
       if(in_hs = '1') then
         nxt_state   <= send4;
         push        <= "00000010000";
       end if;
     when send4 =>
      if(out_hs = '1') then
        nxt_state   <= load5;
      end if;
     when load5 =>
       if(in_hs = '1') then
         nxt_state   <= send5;
         push        <= "00000100000";
       end if;
     when send5 =>
      if(out_hs = '1') then
        nxt_state   <= load6;
      end if;
     when load6 =>
       if(in_hs = '1') then
         nxt_state   <= send6;
         push        <= "00001000000";
       end if;
     when send6 =>
      if(out_hs = '1') then
        nxt_state   <= load7;
      end if;
     when load7 =>
       if(in_hs = '1') then
         nxt_state   <= send7;
         push        <= "00010000000";
       end if;
     when send7 =>
      if(out_hs = '1') then
        nxt_state   <= load8;
      end if;
     when load8 =>
       if(in_hs = '1') then
         nxt_state   <= send8;
         push        <= "00100000000";
       end if;
     when send8 =>
      if(out_hs = '1') then
        nxt_state   <= load9;
      end if;
     when load9 =>
       if(in_hs = '1') then
         nxt_state   <= send9;
         push        <= "01000000000";
       end if;
     when send9 =>
      if(out_hs = '1') then
        nxt_state   <= load10;
      end if;
     when load10 =>
       if(in_hs = '1') then
         nxt_state   <= send10;
         push        <= "10000000000";
       end if;
     when send10 =>
      if(out_hs = '1') then
        if(pkt_zero = '1') then
          nxt_state   <= idle;
        else
          nxt_state   <= load_bypass;
        end if;
      end if;
     when load_bypass =>
       push        <= "00000000000";
       if(in_hs = '1') then
         nxt_state   <= send_bypass;
       end if;
     when wait_idle =>
      if(out_hs = '1') then
        nxt_state   <= idle;
      end if;
    end case;
  end process;

  in2wire: entity work.rdyacpt_c0
    generic map( DATAWIDTH => 8)
    port map(
      upstream_rdy    => di_rdy,
      upstream_acpt   => di_acpt,
      upstream_data   => di,
      downstream_rdy  => in_rdy,
      downstream_acpt => in_acpt,
      downstream_data => input_down_data,
      reset_sync      => reset_n,
      clk             => clk
    );

  pkt_counter: entity work.count
  generic map(WIDTH => 8)
  port map(
    clk   => clk,
    rst_n => reset_n,
    ld_n  => pkt_ld_n,
    up_dn => '0',
    cen   => pkt_cen,
    din   => cnt_din,
--    din   => "11001011",-- 204 - 1 = 203 = 0xcb
    count => pkt_cnt,
    zero  => pkt_zero
    );

  fifo: entity work.fifo_shift_ram
  generic map(BUG => BUG)
  port map(
    clk             => clk,
    reset_n         => reset_n,
    push            => push,
    ram_re          => ram_re,
    din             => input_down_data, 
    sel             => data_sel,
    dout            => fifo_data
  );

  out2wire: entity work.rdyacpt_c0
    generic map( DATAWIDTH => 8)
    port map(
      upstream_rdy    => out_rdy,
      upstream_acpt   => out_acpt,
      upstream_data   => do_reg,
      downstream_rdy  => do_rdy,
      downstream_acpt => do_acpt,
      downstream_data => output_down_data,
      reset_sync      => reset_n,
      clk             => clk
    );

   do_data <= output_down_data(7 downto 0);

end rtl;
