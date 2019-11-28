--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

library IEEE;
  use IEEE.std_logic_1164.all;
entity cache is
  generic( addr_size : Natural := 8;
           word_size : Natural := 16 );
  port (clk    : IN    std_ulogic;
        paddr  : IN    std_logic_vector(addr_size-1 downto 0);
        pdata  : INOUT std_logic_vector(word_size-1 downto 0);
        prw    : IN    std_ulogic;
        pstrb  : IN    std_ulogic;
        prdy   : OUT   std_logic;
        saddr  : OUT   std_logic_vector(addr_size-1 downto 0);
        sdata  : INOUT std_logic_vector(word_size-1 downto 0);
        srw    : OUT   std_ulogic;
        sstrb  : OUT   std_ulogic;
        srdy   : IN    std_ulogic );
end entity cache;

library IEEE;
  use IEEE.numeric_std.all;
architecture RTL of cache is

  constant set_size  : Natural := 5;

  signal verbose : Boolean := TRUE;
  signal sdata_r, pdata_r : std_logic_vector(word_size-1 downto 0) := (others => 'Z');
  signal saddr_r          : std_logic_vector(addr_size-1 downto 0) := (others => '0');
  signal srw_r            : std_ulogic := '0';
  signal sstrb_r          : std_ulogic := '1';
  signal prdy_r           : std_logic := '1';
  signal oen, wen         : std_logic_vector(3 downto 0) := (others => '1');
  signal hit              : std_logic_vector(3 downto 0);
  signal prdy_r_assign    : Boolean := FALSE;
  signal pdata_r_assign   : Boolean := FALSE;
  signal sdata_r_assign   : Boolean := FALSE;

  subtype mru_value is std_logic_vector(2 downto 0);  
  type mru_array is array(0 to 31) of mru_value;
  shared variable mru_mem          : mru_array := (others => (others => '0'));
  
  component cache_set is
    generic(
        addr_size  : integer := 8;
        set_size   : integer := 5;
        word_size  : integer := 16
    );
    port(
        addr            : in    std_logic_vector(addr_size-1 downto 0);
        data            : inout std_logic_vector(word_size-1 downto 0);
        hit             : out   std_logic;
        oen             : in    std_logic;
        wen             : in    std_logic
    );
  end component cache_set;
  
  begin
    saddr <= saddr_r after 5 ns;
    sdata <= sdata_r after 5 ns;
    pdata <= pdata_r after 5 ns;
    srw   <= srw_r after 5 ns;
    sstrb <= sstrb_r after 5 ns;
    prdy  <= prdy_r after 5 ns;
    
    prdy_r <= srdy when prdy_r_assign else 'Z';
    pdata_r <= sdata when pdata_r_assign else (others => 'Z');
    sdata_r <= pdata when sdata_r_assign else (others => 'Z');

    -- **************** Cache sets ****************
    cache_inst0 : cache_set port map (paddr, pdata, hit(0), oen(0), wen(0));
    cache_inst1 : cache_set port map (paddr, pdata, hit(1), oen(1), wen(1));
    cache_inst2 : cache_set port map (paddr, pdata, hit(2), oen(2), wen(2));
    cache_inst3 : cache_set port map (paddr, pdata, hit(3), oen(3), wen(3));

    process
      variable setsel : std_logic_vector(3 downto 0);
      
    -- **************** Cache control ****************/

      impure function get_hit( hit : std_logic_vector(3 downto 0) )
      return std_logic_vector is
        variable setnum : Natural;
        variable result : std_logic_vector(3 downto 0) := (others => '0');
      begin
            if (hit(0) = '1') then
               setnum := 0;
               result := "0001";
            elsif (hit(1) = '1') then
               setnum := 1;
               result := "0010";
            elsif (hit(2) = '1') then
               setnum := 2;
               result := "0100";
            elsif (hit(3) = '1') then
               setnum := 3;
               result := "1000";
            end if;
            if (verbose) then
                if (prw = '1') then
                    report time'image(now) & ": Read hit to set " & integer'image(setnum);
                else
                    report time'image(now) & ": Write hit to set " & integer'image(setnum);
                end if;
            end if;
            return result;
      end function get_hit;
     
      -- **************** Local MRU memory ****************/

      function hash(a : std_logic_vector(addr_size-1 downto 0)) return integer is
      begin
        return to_integer(unsigned(a(set_size-1 downto 0)));
      end function hash;

      procedure update_mru ( addr : std_logic_vector(addr_size-1 downto 0);
                             hit  : std_logic_vector(3 downto 0) )
      is
        variable mru_val : mru_value;
        variable mru_index : natural := hash(addr);
      begin
            mru_val := mru_mem(mru_index);
            if (hit and "1100") /= "0000" then
              mru_val(2) := '1';
            else
              mru_val(2) := '0';
            end if;
            if (mru_val(2) = '1') then
              mru_val(1) := hit(3);
            else
              mru_val(0) := hit(1);
            end if;
            mru_mem(mru_index) := mru_val;
      end procedure update_mru;

      impure function pick_set( addr : std_logic_vector(addr_size-1 downto 0) )
      return std_logic_vector is
        variable setnum : Natural;
        variable mru_val : mru_value;
        variable result : std_logic_vector(3 downto 0) := (others => '0');
      begin
        mru_val := mru_mem(hash(addr));
        if (mru_val(2) = '1') and (mru_val(0) = '1') then
           setnum := 0;
           result := "0001";
        elsif (mru_val(2) = '1') and (mru_val(0) = '0') then
           setnum := 1;
           result := "0010";
        elsif (mru_val(2) = '0') and (mru_val(1) = '1') then
           setnum := 2;
           result := "0100";
        elsif (mru_val(2) = '0') and (mru_val(1) = '0') then
           setnum := 3;
           result := "1000";
        else
           setnum := 0;
           result := "0001";
        end if;
        if (verbose) then
          if (prw = '1') then
             report time'image(now) & ": Read miss, picking set " & integer'image(setnum);
          else
             report time'image(now) & ": Write mis, picking set " & integer'image(setnum);
          end if;
        end if;
        return result;
            
      end function pick_set;
    
      -- **************** System Bus interface ****************/
      procedure sysread( a : std_logic_vector(addr_size-1 downto 0)) is
      begin
        saddr_r <= a;
        srw_r <= '1';
        sstrb_r <= '0';
        wait until clk'event and clk = '1';
        sstrb_r <= '1';
        prdy_r <= 'Z';
        prdy_r_assign <= TRUE;
        pdata_r_assign <= TRUE;
        wait until clk'event and clk = '1';
        while (srdy /= '0') loop
          wait until clk'event and clk = '1';
        end loop;
        prdy_r_assign <= FALSE;
        pdata_r_assign <= FALSE;
        prdy_r <= '1';
      end procedure sysread;

      procedure syswrite (a : std_logic_vector(addr_size-1 downto 0)) is
      begin
        saddr_r <= a;
        srw_r <= '0';
        sstrb_r <= '0';
        wait until clk'event and clk = '1';
        sstrb_r <= '1';
        prdy_r <= 'Z';
        prdy_r_assign <= TRUE;
        sdata_r_assign <= TRUE;
        wait until clk'event and clk = '1';
        while (srdy /= '0') loop
          wait until clk'event and clk = '1';
        end loop;
        prdy_r_assign <= FALSE;
        sdata_r_assign <= FALSE;
        prdy_r <= '1';
      end procedure syswrite;
        
    begin
      wait until clk'event and clk = '1';
      if (pstrb = '0') then
        if (prw = '1') and (hit /= "0000") then
            -- Read Hit..
            setsel := get_hit(hit);
            oen <= not(setsel);
            prdy_r <= '0';
            wait until clk'event and clk = '1';
            prdy_r <= '1';
            oen <= "1111";
        else
            -- Read Miss or Write Hit..
            if (hit /= "0000") then
                setsel := get_hit(hit);
            else
                setsel := pick_set(paddr);
            end if;
            wen <= not(setsel);
            if (prw = '1') then
                sysread (paddr);
            else
                syswrite(paddr);
            end if;
            wen <= "1111";
        end if;
        update_mru(paddr, setsel);
      end if;
    end process;
    
end architecture RTL;
