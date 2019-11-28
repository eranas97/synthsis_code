library ieee;
    use ieee.std_logic_1164.all;
    use ieee.std_logic_unsigned.all;

entity ram2p_2kx8 is
  port (
    wclk   : in  std_logic;
    din    : in  std_logic_vector(7 downto 0);
    waddr  : in  std_logic_vector(10 downto 0);
    we     : in  std_logic;
    re     : in  std_logic;
    rclk   : in  std_logic;
    raddr  : in  std_logic_vector(10 downto 0);
    dout   : out std_logic_vector(7 downto 0)
    );
end ram2p_2kx8;

architecture behav of ram2p_2kx8 is

  type mem_array is array (2047 downto 0) of std_logic_vector(7 downto 0);
  signal ram     : mem_array;
  signal oreg    : std_logic_vector(7 downto 0);

begin
 
  dout <= oreg;

  process(rclk)
  begin
    if(rising_edge(rclk)) then
      if(re = '1') then
        oreg <= ram(conv_integer(raddr));
      else
        oreg <= oreg;
      end if;
    end if;
  end process;

  process(wclk)
  begin
    if(rising_edge(wclk)) then  
      if(we = '1') then
        ram(conv_integer(waddr)) <= din;
      end if;
    end if;
  end process;

end behav;
