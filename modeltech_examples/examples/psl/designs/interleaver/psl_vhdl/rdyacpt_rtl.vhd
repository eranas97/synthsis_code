library ieee;
use ieee.std_logic_1164.all;

--The architecture of the rdyacpt stage uses 2 sets of registers to break the
--feedback timing of pipeline enables. The primary data pipe stage is d0 (v0 set when
--its valid). The sidecar register (d1,v1) is utilized when the downstream_acpt is
--deasserted.

architecture rtl of rdyacpt_c0 is
    constant all_zeros : std_logic_vector(DATAWIDTH-1 downto 0) := (others => '0');

    signal d0, d1 : std_logic_vector(DATAWIDTH-1 downto 0);
    signal v0, v1, ready_reg : std_logic;
  
    signal v0_sel, en_v0, en_v1 : std_logic;


begin

    en_v0  <= NOT v0 OR downstream_acpt;
    en_v1  <= NOT v1 OR ready_reg;
    v0_sel <= en_v0 AND v1 AND NOT ready_reg;
    upstream_acpt   <= NOT v1 OR ready_reg;
    downstream_rdy  <= v0;
    downstream_data(DATAWIDTH-1 downto 0) <= d0;

    pipe_empty    <= NOT v0 AND NOT v1;
    pipe_notempty <= v0 OR v1;
    

    valid_flags : process (clk,reset_sync)
    begin
        if reset_sync = '0' then
            v0 <= '0';
            v1 <= '0';
        elsif clk='1' and clk'event then
            if en_v0 = '1' then
               if v0_sel = '1' then
                  v0 <= v1;
               else
                  v0 <= upstream_rdy;
               end if;
            end if;

            if en_v1 = '1' then
               v1 <= upstream_rdy;
            end if;

        end if;
    end process valid_flags;

    ready_and_data : process (clk)
    begin
        if clk='1' and clk'event then
            ready_reg <= downstream_acpt OR NOT v0;
            if en_v0 = '1' then
               if v0_sel = '1' then
                  d0 <= d1;
               elsif ((HOLDOUT = 1) AND (upstream_rdy = '1')) OR (HOLDOUT = 0) then
                  d0 <= upstream_data(DATAWIDTH-1 downto 0);
               end if;
            end if;

            if en_v1 = '1' then
               d1 <= upstream_data(DATAWIDTH-1 downto 0);
            end if;

        end if;
    end process ready_and_data;


end rtl;

