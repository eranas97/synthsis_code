--------------------------------------------------------------
-- Clock generator
--   Period can be enabled to vary to +/- clk_var by clk_stp
--   every period. Amount of step can also be enabled to 
--   be randomized to the range of clk_stp/2 to clk_stp.
--------------------------------------------------------------
library work;
library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_arith.all;
use ieee.std_logic_unsigned.all;

use std.textio.all;
use ieee.math_real.all;
use work.io_utils.all;
Use work.rng.All;    --random number stuff   

entity clkgen is
generic( clk_per,clk_var: time;
         clk_idel, clk_jit: time := 0 ps;
         drift_rate : integer := 20000;              -- 20khz default drift
         do_drift: boolean := false;       -- drift clk period within clk_var
         do_jitter: boolean := false);     -- randomly adjust period
port ( clk    : buffer std_logic);
end;
       

architecture beh of clkgen is
   signal iclk : std_logic := '0';
   signal sdir : std_logic;
   --signal sdir : std_logic;
   shared variable cstp: time ;
   --random clk step if enabled
   shared variable rcstp: time ;
   shared variable dir: integer := 1;
   shared variable cper, bper: time := clk_per;
   shared variable l : line;
   file ouput: TEXT open write_mode is "STD_OUTPUT";

begin

clk_gen : process 
variable num_steps,drift_per : real;
variable steps, skips, skip_cnt     : integer;
begin
   skip_cnt := 0;

   --some intitial calcs for performing the drift from the input given as a rate
   if do_drift then
      --num_steps := real(time'pos(clk_per * drift_rate))/1000.0;
      drift_per := 1.0/real(drift_rate);
      --div number of steps by 4 since only looking at 1/4 period
      num_steps := drift_per / ((real(time'pos(clk_per))/1.0e+15) * 4.0) ;
      steps := integer(num_steps); 
      while (steps > 1) AND ((clk_var / steps) < 1 ps) loop
         steps := steps / 10;
      end loop;

      skips := integer(num_steps) / steps;
      cstp  := clk_var / steps;
 
      --write(l, string'("clk_per="));
      --write(l, clk_per );
      --write(l, string'(" drift_rate="));
      --write(l, drift_rate );
      --write(l, string'(" num steps="));
      --write(l, num_steps );
      --write(l, string'(" clk_var="));
      --write(l, clk_var );
      --write(l, string'(" steps="));
      --write(l, steps );
      --write(l, string'(" skips="));
      --write(l, skips );
      --write(l, string'(" cstp="));
      --write(l, cstp );
      --writeline(output, l);
      --          assert false                                                                
      --          report "sim over"            
      --          severity failure;
   end if;


   wait for clk_idel;
   loop
      --write(l, string'(" cper="));
      --write(l, cper );
      --write(l, string'(" skipcnt="));
      --write(l, skip_cnt );
      --write(l, string'(" dir="));
      --write(l, dir );
      --write(l, string'(" at "));
      --write(l, now );
      --writeline(output, l);

      iclk <= '1' after cper/2 , '0' after cper ;
      wait for cper;
      if do_drift then 
         skip_cnt := skip_cnt + 1;
         if skip_cnt >= skips then
            --adjust base period
            skip_cnt := 0;
            if (dir > 0) then bper := bper + cstp;
            else              bper := bper - cstp;
            end if;
         end if;
      end if;

      if do_jitter then cper := bper + rcstp;
      else              cper := bper;
      end if;

      if (abs(clk_per - bper) >=  clk_var) then
         if ( bper > clk_per) then dir := -1;
         else dir := 1;
         end if;
      end if;
      if (dir < 0) then
         sdir <= '1' ;
      else 
         sdir <= '0' ;
      end if;
      end loop;
end process clk_gen;


   rnd: process
   variable rnum,rnum1,cnum,rjit : real;
   variable i : integer;
   variable seed1,seed2: positive ;
   Variable rnd_rec: normal ;
   begin
      seed1 := 1;
      seed2 := 3;
      rnd_rec := initnormal(33,0.0,1.0);
      loop
        --uniform(seed1,seed2, rnum);
        --divide by 1000 for unit correction
        genrnd(rnd_rec);
        rnum1 := (rnd_rec.rnd + 3.3) / 6.6; --make it 0 - 1

        rjit := real(time'pos(clk_jit));
        rnum := rnum1 * rjit / 1000.0 ; 
        i := integer(rnum) ;
        --rcstp := (i * 1 ps) - (clk_jit / 2);
        rcstp := (clk_jit / 2) - (i * 1 ps);

        if do_jitter then
        --print out clk step and randomly adjusted step
	--write(l, clk_jit );
	--write(l, string'("  "));
	--write(l, rcstp );
	--write(l, string'(" cper="));
	--write(l, cper );
	--write(l, string'(" rjit="));
	--write(l, rjit );
	--write(l, string'(" randnum="));
	--write(l, rnum1 );
        --writeline(output, l);
        end if;

        wait for clk_per;
     end loop;
   end process rnd;

   clk <= iclk;

end ;


