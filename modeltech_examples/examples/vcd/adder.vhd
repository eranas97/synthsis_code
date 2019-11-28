--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   
------------------------------------------------------------------------
-- Single-bit adder
------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
entity adder is
    port (a    : in std_logic;
          b    : in std_logic;
          cin  : in std_logic;
          sum  : out std_logic;
          cout : out std_logic);
end adder;


-- description of adder using concurrent signal assignments
architecture rtl of adder is
begin
    sum <= (a xor b) xor cin;
    cout <= (a and b) or (cin and a) or (cin and b);
end rtl;


-- description of adder using component instantiation statements
use work.gates.all;
architecture structural of adder is
    signal xor1_out,
	   and1_out,
	   and2_out,
	   or1_out : std_logic;
begin
    xor1: xorg port map(
		in1  => a,
		in2  => b,
		out1 => xor1_out);
    xor2: xorg port map(
		in1 => xor1_out,
		in2 => cin,
		out1 => sum);
    and1: andg port map(
		in1 => a,
		in2 => b,
		out1   => and1_out);
    or1: org port map(
		in1 => a,
		in2 => b,
		out1   => or1_out);
    and2: andg port map(
		in1 => cin,
		in2 => or1_out,
		out1   => and2_out);
    or2: org port map(
		in1 => and1_out,
		in2 => and2_out,
		out1   => cout);
end structural;


------------------------------------------------------------------------
-- N-bit adder
-- The width of the adder is determined by generic N
------------------------------------------------------------------------
library IEEE;
use IEEE.std_logic_1164.all;
entity adderN is
    generic(N : integer := 16);
    port (a    : in std_logic_vector(N downto 1);
          b    : in std_logic_vector(N downto 1);
          cin  : in std_logic;
          sum  : out std_logic_vector(N downto 1);
          cout : out std_logic);
end adderN;

-- structural implementation of the N-bit adder
architecture structural of adderN is
    component adder
        port (a    : in std_logic;
              b    : in std_logic;
              cin  : in std_logic;
              sum  : out std_logic;
              cout : out std_logic);
    end component;

    signal carry : std_logic_vector(0 to N);
begin
    carry(0) <= cin;
    cout <= carry(N);

    -- instantiate a single-bit adder N times
    gen: for I in 1 to N generate
	add: adder port map(
		a => a(I),
		b => b(I),
		cin => carry(I - 1),
		sum => sum(I),
		cout => carry(I));
   end generate;
end structural;


-- behavioral implementation of the N-bit adder
architecture behavioral of adderN is
begin
    p1: process(a, b, cin)
	variable vsum : std_logic_vector(N downto 1);
	variable carry : std_logic;
    begin
	carry := cin;
	for i in 1 to N loop
	    vsum(i) := (a(i) xor b(i)) xor carry;
	    carry := (a(i) and b(i)) or (carry and (a(i) or b(i)));
	end loop;
	sum <= vsum;
	cout <= carry;
    end process p1;
end behavioral;

