--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

library ieee;
use ieee.std_logic_1164.all;
use work.std_logic_util.all;

entity cache_set is
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
end cache_set;

architecture only of cache_set is
    constant size : integer := 2**set_size;
    constant dly : time := 5 ns;
    subtype word_t is std_logic_vector(word_size-1 downto 0);
    subtype addr_t is std_logic_vector(addr_size-1 downto 0);
    type mem_t is array (0 to size-1) of word_t;
    subtype tag_word_t is std_logic_vector(addr_size-1 downto set_size);
    type tag_t is array (0 to size-1) of tag_word_t;
    type valid_t is array (0 to size-1) of boolean;
    signal data_out : word_t;
begin

    data <= (others => 'Z') after dly when (oen = '1') else data_out after dly;

    process(wen, addr)
        ---------- Local tag and data memories -----------
        variable data_mem : mem_t;
        variable atag_mem : tag_t;
        variable valid_mem : valid_t := (others => false);

        function hash(constant a : addr_t) return integer is
        begin
            return conv_integer(a(set_size-1 downto 0));
        end;

        procedure lookup_cache(constant a : addr_t) is
            variable i : integer;
            variable found : boolean;
        begin
            i := hash(a);
            found := valid_mem(i) and (a(tag_word_t'range) = atag_mem(i));
            if found then
                hit <= '1' after dly;
            else
                hit <= '0' after dly;
            end if;
        end;

        procedure update_cache(constant a : addr_t;
                               constant d : word_t) is
            variable i : integer;
        begin
            i := hash(a);
            data_mem(i) := d;
            atag_mem(i) := a(tag_word_t'range);
            valid_mem(i) := true;
        end;

    begin
        if wen'event and (wen = '1') then
            update_cache(addr, data);
        end if;

        lookup_cache(addr);

        data_out <= data_mem(hash(addr));
    end process;
end;

