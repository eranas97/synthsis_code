library ieee;
    use ieee.std_logic_1164.all;


entity rdyacpt_c0 is -- Symbol_Width 20 Symbol_Height 20
generic (
    DATAWIDTH   : integer := 8;
    FLAGWIDTH   : integer := 0;
    HOLDOUT     : integer := 0
    );

port (
    upstream_rdy    : in  std_logic;
    upstream_acpt   : out std_logic;
    upstream_data   : in  std_logic_vector (FLAGWIDTH + DATAWIDTH-1 downto 0);
    downstream_rdy  : out std_logic;
    downstream_acpt : in  std_logic;
    downstream_data : out std_logic_vector (FLAGWIDTH + DATAWIDTH-1 downto 0);
    pipe_empty      : out std_logic;  -- optional
    pipe_notempty   : out std_logic;  -- optional
    reset_sync      : in  std_logic;
    clk             : in  std_logic
    );
end rdyacpt_c0; -- Default_Architecture rtl

