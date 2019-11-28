library work;
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;
use std.textio.all;
use ieee.math_real.all;
Use work.rng.All;    --random number stuff   

entity interleaver_tester is
generic (
     RUNFC                        : integer  :=0
     );

end entity interleaver_tester;

architecture behave of interleaver_tester is


  constant  WIDTH_IN    : integer := 8;
  constant  WIDTH_OUT   : integer := 8;
--  constant  DELAY_MULT  : integer := 17;
--  constant  LEVEL_NUM   : integer := 12;
--  constant  REG_NUM     : integer := 1122;

   type SHIFT_REG is array (0 to 1121) of std_logic_vector(WIDTH_IN-1 downto 0);


--Clock parameters for simulation
   constant clk_do_drift : boolean := false;
   constant clk_do_jitter: boolean := false;

--Symbol clk parms
   constant clk_idel: time := 0.0 ns;
   constant clk_per : time := 10.0 ns;
   constant clk_jit : time :=  1.0 ns;

   constant clk_var : time := 3 ns;
   constant clk_drift_rate : integer := 20000; -- 20khz
   constant all_zeros : std_logic_vector(WIDTH_IN-1 downto 0) := (others => '0');

   signal  reset,clk,upstream_rdy,upstream_acpt,downstream_rdy,downstream_acpt: std_logic;
   signal  upstream_data, prev_upstream_data : std_logic_vector(WIDTH_IN-1 downto 0);
   signal  downstream_data, prev_downstream_data : std_logic_vector(WIDTH_OUT-1 downto 0);
   signal  expected_data : std_logic_vector(WIDTH_OUT-1 downto 0);
   signal  cmp_fifo_data : std_logic_vector(WIDTH_OUT-1 downto 0);
   signal  cmp_fifo_push : std_logic;
   signal  cmp_fifo_pop  : std_logic;

   signal  reg_addr : std_logic_vector ( 7 downto 0);
   signal  pipe_reg : SHIFT_REG;

   signal  up_hs_less10_cnt : std_logic_vector(WIDTH_OUT downto 0);

  -- psl default clock is rising_edge(clk);

  -- Check RTL do with behavior model
  -- p sl property data_delay_check is always {downstream_rdy = '1' AND downstream_acpt = '1'} |->
  -- psl property data_delay_check is always {downstream_rdy AND downstream_acpt} |->
  -- { cmp_fifo_data = downstream_data };
  -- psl assert data_delay_check;

  -- Check for upstream rdy acpt handshake
  -- psl property up_hs_check is always (upstream_rdy -> eventually!( upstream_acpt));
  -- psl assert up_hs_check;

  -- Check for downstream rdy acpt handshake
  -- psl property dwn_hs_check is always (downstream_rdy -> eventually! (downstream_acpt));
  -- psl assert dwn_hs_check;

  -- Check for upstream data to hold if acpt de-asserted
  -- using an external register for data comparse since
  -- builtin prev function not supported yet when it is
  -- supported then {upstream_data = prev(upstream_data}
  -- is how the second half of the property should be written
  -- psl property up_data_hold_check is always {upstream_rdy AND NOT upstream_acpt} |=>
  --   {upstream_data = prev(upstream_data)};
  -- psl assert up_data_hold_check;

  -- psl sequence s_no_up_hs_less_10 is {rose(upstream_rdy AND NOT upstream_acpt);
  --                                   (upstream_rdy AND NOT upstream_acpt)[*0 to 10];
  --                                   (upstream_rdy AND upstream_acpt)};

  -- psl c_no_up_hs_less_10: cover s_no_up_hs_less_10;

  -- psl sequence up_hs_less10_hit is {s_no_up_hs_less_10}@(rising_edge(clk));

  -- psl sequence s_no_up_hs_more_10 is {rose(upstream_rdy AND NOT upstream_acpt);
  --                                   (upstream_rdy AND NOT upstream_acpt)[*11 to inf];
  --                                    upstream_rdy AND upstream_acpt};

  -- psl c_no_up_hs_more_10: cover s_no_up_hs_more_10;

  -- Check for downstream data to hold if acpt de-asserted
  -- using an external register for data comparse since
  -- builtin prev function not supported yet when it is
  -- supported then {downstream_data = prev(downstream_data}
  -- is how the second half of the property should be written
  -- using an external register for data comparse since builtin prev function not supported yet
  -- psl property dwn_data_hold_check is always {downstream_rdy AND NOT downstream_acpt} |=>
  --   {downstream_data = prev(downstream_data)};
  -- psl assert dwn_data_hold_check;

  -- psl sequence s_no_dwn_hs_less_10 is {rose(downstream_rdy AND NOT downstream_acpt);
  --                                   (downstream_rdy AND NOT downstream_acpt)[*0 to 10];
  --                                    downstream_rdy AND downstream_acpt};

  -- psl c_no_dwn_hs_less_10: cover s_no_dwn_hs_less_10;

  -- psl sequence s_no_dwn_hs_more_10 is {rose(downstream_rdy AND NOT downstream_acpt);
  --                                   (downstream_rdy AND NOT downstream_acpt)[*11 to inf];
  --                                    downstream_rdy AND downstream_acpt};

  -- psl c_no_dwn_hs_more_10: cover s_no_dwn_hs_more_10;

   begin

        input_clock : entity work.clkgen                        -- Byte clock generator
                generic map(
                        clk_per => clk_per,
                        clk_jit => clk_jit,
                        clk_var => clk_var,
                        drift_rate => clk_drift_rate,
                        do_drift=>    clk_do_drift,
                        do_jitter=>   clk_do_jitter
                )
                port map(
                        clk             => clk
                );

        interleaver1 : entity work.interleaver_m0
                generic map(
                        BUG => 1
                )
                port map(
                        clk       => clk,
                        reset_n   => reset,
                        di_rdy    => upstream_rdy,
                        di_acpt   => upstream_acpt,
                        di        => upstream_data,
                        do_rdy    => downstream_rdy,
                        do_acpt   => downstream_acpt,
                        do_data   => downstream_data,
                        enable   => '1'
 
                );

        cmp_fifo : entity work.fifo                        -- fifo comparitor
                generic map(
                        DEPTH => 64,
                        SIZE => 6,
                        WIDTH=> 8
                )
                port map(
                        clk     => clk,
                        reset_n => reset,
                        din     => expected_data,
                        push    => cmp_fifo_push,
                        pop     => cmp_fifo_pop,
                        dout    => cmp_fifo_data
                );

       process is                                     -- Reset generator
        begin
                reset <= '0', '1' after 100 ns;
                wait;
--                assert false
--                report "sim over"
--                severity failure;
        end process;

       process (clk, reset) is
         variable less10_hit : boolean;
         begin
           if (reset = '0') then
             up_hs_less10_cnt <= (others => '0');
           elsif (rising_edge (clk)) then
             less10_hit := ended(up_hs_less10_hit);
             if (RUNFC = 1) then
               if (less10_hit) then
                 if (up_hs_less10_cnt = "100000000") then
                   up_hs_less10_cnt <= (others => '0');
                 else
                   up_hs_less10_cnt <= up_hs_less10_cnt + 1;
                 end if;
               end if;
             else
               up_hs_less10_cnt <= (others => '0');
             end if;
           end if;
         end process;
           
           


stim_proc:  process is                                     -- stim interface
        
        variable new_rdy : std_logic;
        variable new_data : std_logic_vector(WIDTH_IN-1 downto 0) := "00000000";
        variable rnum1: real;
        variable seed1,seed2: positive ;
        Variable rnd_rec: normal ;
        variable i,j : integer := 0;
        begin
           seed1 := 1;
           seed2 := 3;
           rnd_rec := initnormal(33,0.0,1.0);

           loop
                if reset = '1' then
                   if (upstream_rdy = '1' AND upstream_acpt = '1') then
                      new_rdy := '0'; -- we'll do the next transaction
                   end if;
                   if (new_rdy = '0') then
                      genrnd(rnd_rec); 
                      rnum1 := (rnd_rec.rnd + 3.3) / 6.6; --make it 0 - 1
                      if (rnum1 > 0.5) then 
                         new_rdy := '1';
                         if (i = 0) then
                           if (j = 0) then
                             new_data := "10111000";
                           else
                             new_data := "01000111";
                           end if;
                         else
                           new_data := CONV_STD_LOGIC_VECTOR(((j*1000)+i),new_data'length);
                           --new_data := new_data + "00000001";
                           --if (new_data = "10111000" OR new_data = "01000111") then
                            -- new_data := "00000001";
                           --end if;
                         end if;
                         if (i = 203) then
                           i := 0;
                           if (j = 7) then
                             j := 0;
                           else
                             j := j + 1;
                           end if;
                         else
                           i := i + 1;
                         end if;
                      end if;
                   end if;
                else 
                   new_rdy := '0';
                   new_data := all_zeros;
                end if;
               
                upstream_rdy <= new_rdy;
                if (new_rdy = '1') then 
                   upstream_data <= new_data;
                else
                  upstream_data <= all_zeros;
                end if;
                   
                wait until rising_edge(clk);
           end loop;
        end process stim_proc;

resp_proc:  process is                                     -- resp interface
        variable new_acpt : std_logic;
        variable new_data : std_logic_vector(WIDTH_OUT-1 downto 0);
        variable rnum1: real;
        variable seed1,seed2: positive ;
        Variable rnd_rec: normal ;
        begin
           seed1 := 1;
           seed2 := 3;
           rnd_rec := initnormal(13,0.0,1.0);

           loop
                if reset = '1' then
                   if (downstream_rdy = '1' AND downstream_acpt = '1') then
                      new_acpt := '0'; -- we'll do the next transaction
                   end if;
                   if (new_acpt = '0') then
                      genrnd(rnd_rec); 
                      rnum1 := (rnd_rec.rnd + 3.3) / 6.6; --make it 0 - 1
                      if (up_hs_less10_cnt < "010000000") then
                         if (rnum1 > 0.5) then 
                            new_acpt := '1';
                         end if;
                      else
                         if (rnum1 > 0.7) then 
                            new_acpt := '1';
                         end if;
                      end if;
                   end if;
                else 
                   new_acpt := '0';
                end if;
               
                downstream_acpt <= new_acpt;
                   
                wait until rising_edge(clk);
           end loop;
        end process resp_proc;

    cmp_fifo_pop <= downstream_rdy AND downstream_acpt;

check_data:  process (clk, reset)
  variable k, j : integer;
  begin
  if (reset = '0') then
    k := 0;
    cmp_fifo_push <= '0';
    --cmp_fifo_pop <= '0';
  elsif (rising_edge(clk)) then
    if ( downstream_rdy = '1' AND downstream_acpt = '1') then
      if (cmp_fifo_data /= downstream_data) then
        report "Data Misscompare ERROR at time " & time'image(now) severity FAILURE;
      end if;
      --cmp_fifo_pop <= '1';
    elsif ( downstream_rdy = '1' AND downstream_acpt = '0') then
      prev_downstream_data <= downstream_data;
      --cmp_fifo_pop <= '0';
    end if;
    if ( upstream_rdy = '1' AND upstream_acpt = '1') then
      cmp_fifo_push <= '1';
      case k is
        when 0 =>
          expected_data <= upstream_data;
        when 1 =>
          expected_data <= pipe_reg(16);
          for j in 16 downto 0 loop
            if (j = 0) then
              pipe_reg(0) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when 2 =>
          expected_data <= pipe_reg(50);
          for j in 50 downto 17 loop
            if (j = 17) then
              pipe_reg(17) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when 3 =>
          expected_data <= pipe_reg(101);
          for j in 101 downto 51 loop
            if (j = 51) then
              pipe_reg(51) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when 4 =>
          expected_data <= pipe_reg(169);
          for j in 169 downto 102 loop
            if (j = 102) then
              pipe_reg(102) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when 5 =>
          expected_data <= pipe_reg(254);
          for j in 254 downto 170 loop
            if (j = 170) then
              pipe_reg(170) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when 6 =>
          expected_data <= pipe_reg(356);
          for j in 356 downto 255 loop
            if (j = 255) then
              pipe_reg(255) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when 7 =>
          expected_data <= pipe_reg(475);
          for j in 475 downto 357 loop
            if (j = 357) then
              pipe_reg(357) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when 8 =>
          expected_data <= pipe_reg(611);
          for j in 611 downto 476 loop
            if (j = 476) then
              pipe_reg(476) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when 9 =>
          expected_data <= pipe_reg(764);
          for j in 764 downto 612 loop
            if (j = 612) then
              pipe_reg(612) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when 10 =>
          expected_data <= pipe_reg(934);
          for j in 934 downto 765 loop
            if (j = 765) then
              pipe_reg(765) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when 11 =>
          expected_data <= pipe_reg(1121);
          for j in 1121 downto 935 loop
            if (j = 935) then
              pipe_reg(935) <= upstream_data;
            else
              pipe_reg(j) <= pipe_reg(j-1);
            end if;
          end loop;
        when others =>
          null;
      end case;
      if (k = 11) then
        k := 0;
      else
        k := k + 1;
      end if;
    else
      cmp_fifo_push <= '0';
      if (upstream_rdy = '1' AND upstream_acpt = '0') then
        prev_upstream_data <= upstream_data;
      end if;
    end if;
  end if;
end process check_data;


end architecture behave;
                 
