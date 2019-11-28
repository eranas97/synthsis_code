library ieee;
    use ieee.std_logic_1164.all;
    use ieee.std_logic_unsigned.all;

entity fifo is
  generic ( DEPTH  : integer := 256;
            SIZE   : integer := 8;
            WIDTH  : integer := 8
  );
  port (
    clk     : in  std_logic;
    reset_n : in  std_logic;
    din     : in  std_logic_vector(7 downto 0);
    push    : in  std_logic;
    pop     : in  std_logic;
    dout    : out std_logic_vector(7 downto 0)
    );
end fifo;

architecture behav of fifo is

  type mem_array is array (DEPTH-1 downto 0) of std_logic_vector(WIDTH-1 downto 0);
  signal ram     : mem_array;
--  signal oreg    : std_logic_vector(WIDTH-1 downto 0);
  signal waddr    : std_logic_vector(SIZE-1 downto 0);
  signal raddr    : std_logic_vector(SIZE-1 downto 0);

begin
 
--  dout <= oreg;
  dout <= ram(conv_integer(raddr));

  process(clk, reset_n)
  begin
    if (reset_n = '0') then
      waddr <= (others => '0');
    elsif (rising_edge(clk)) then
      if(push = '1') then
        ram(conv_integer(waddr)) <= din;
        waddr <= waddr + 1;
      end if;
    end if;
  end process;

  process(clk, reset_n)
  begin
    if (reset_n = '0') then
      raddr <= (others => '0');
    elsif (rising_edge(clk)) then
      if(pop = '1') then
        raddr <= raddr + 1;
      end if;
    end if;
  end process;

end behav;

