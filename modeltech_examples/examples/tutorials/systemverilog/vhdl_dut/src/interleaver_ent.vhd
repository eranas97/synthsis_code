library IEEE;
use IEEE.STD_LOGIC_1164.ALL;

entity interleaver_m0 is
  generic (
     PORTA_MAX_ADDR_SIZE        : NATURAL  :=11;
     BUG                        : INTEGER  :=0
     );
  port (
    clk             : in  std_logic;
    reset_n         : in  std_logic;
--    scan_enable     : in  std_logic;
    di_rdy          : in  std_logic;
    di              : in  std_logic_vector(7 downto 0);
    do_acpt         : in  std_logic;
    do_data         : out std_logic_vector(7 downto 0);
--    do              : out std_logic_vector(7 downto 0);
    di_acpt         : out std_logic;
    do_rdy          : out std_logic;
--    sw_reset        : in std_logic;
    enable          : in std_logic
  );
end interleaver_m0 ;

