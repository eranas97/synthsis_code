library ieee;
use ieee.std_logic_1164.all;
use ieee.std_logic_unsigned.all;

entity count is
  generic ( WIDTH : integer := 8);
  port (
    ----------------------------------------------------------------------------
    clk     : in  std_logic;  -- clock
    rst_n   : in  std_logic;  -- active low reset
    ld_n    : in  std_logic;  -- active low load
    up_dn   : in  std_logic;  -- count up or down
    cen     : in  std_logic;  -- active high count enable
    din     : in  std_logic_vector(WIDTH-1 downto 0);  -- input load data
    ----------------------------------------------------------------------------
    count   : out std_logic_vector(WIDTH-1 downto 0);  -- count output
    tc      : out std_logic;  -- maximum count
    zero    : out std_logic   -- count is zero;
  );
end count ;

architecture RTL of count is

  signal ltiex : std_logic_vector(WIDTH-1 downto 0);
  signal htiex : std_logic_vector(WIDTH-1 downto 0);
  signal count_l : std_logic_vector(WIDTH-1 downto 0);

begin

  ltiex <= (others => '0');
  htiex <= (others => '1');
  count <= count_l;
  tc    <= '1' when (count_l = htiex) else '0';
  zero  <= '1' when (count_l = ltiex) else '0';

  process(clk, rst_n)
  begin
    if (rst_n = '0') then
      count_l <= ltiex;
    elsif(rising_edge(clk)) then
      if (ld_n = '0') then
        count_l <= din;
      else
        if (cen = '0') then
          count_l <= count_l;
        else
          case up_dn is
            when '1' =>    count_l <= count_l + 1;
            when others => count_l <= count_l - 1;
          end case;
        end if;
      end if;
    end if;
end process;

end RTL;
