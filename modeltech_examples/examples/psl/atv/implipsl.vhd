entity implipsl is
end implipsl;

architecture arch of implipsl is

	signal clk  : bit := '0';
	signal b0   : bit := '0';
	signal b1   : bit := '0';
	signal b2   : bit := '0';
	signal b3   : bit := '0';
	signal b4   : bit := '0';
	signal b5   : bit := '0';

begin

clk     <= not clk after 50 ns;

-- psl default clock is (clk'event and clk = '1');
-- psl property p2 is {b2} |=> {{b2[*2]} && {b3; b4}};
-- psl property p1 is {b0; b1[*2 to 3]} (p2);
-- psl property p0 is always b0 -> p1;
-- psl assert p0;
-- sl property p2 is {b2} |=> {{b2[*1 to 2]} && {b3; [*0 to 1]; b4}};

process
begin
	wait for 100 ns;     b0 <= '1';   b1 <= '0';   b2 <= '0';   b3 <= '0';   b4 <= '0';  --100
	wait for 100 ns;     b0 <= '0';   b1 <= '1';   b2 <= '0';   b3 <= '0';   b4 <= '0';  --200
	wait for 100 ns;     b0 <= '1';   b1 <= '1';   b2 <= '0';   b3 <= '1';   b4 <= '0';  --300
	wait for 100 ns;     b0 <= '0';   b1 <= '1';   b2 <= '0';   b3 <= '1';   b4 <= '0';  --400
	wait for 100 ns;     b0 <= '0';   b1 <= '1';   b2 <= '0';   b3 <= '0';   b4 <= '0';  --500
	wait for 100 ns;     b0 <= '0';   b1 <= '1';   b2 <= '1';   b3 <= '1';   b4 <= '0';  --600
	wait for 100 ns;     b0 <= '0';   b1 <= '1';   b2 <= '1';   b3 <= '1';   b4 <= '0';  --700
	wait for 100 ns;     b0 <= '0';   b1 <= '0';   b2 <= '1';   b3 <= '1';   b4 <= '1';  --800
	wait for 100 ns;     b0 <= '1';   b1 <= '1';   b2 <= '0';   b3 <= '0';   b4 <= '0';  --900
	wait for 100 ns;     b0 <= '0';   b1 <= '1';   b2 <= '0';   b3 <= '0';   b4 <= '0';  --1000
	wait for 100 ns;     b0 <= '0';   b1 <= '1';   b2 <= '0';   b3 <= '0';   b4 <= '0';  --1100
	wait for 100 ns;     b0 <= '0';   b1 <= '0';   b2 <= '1';   b3 <= '1';   b4 <= '0';  --1200
	wait for 100 ns;     b0 <= '0';   b1 <= '0';   b2 <= '1';   b3 <= '0';   b4 <= '0';  --1300
	wait for 100 ns;     b0 <= '0';   b1 <= '0';   b2 <= '1';   b3 <= '0';   b4 <= '1';  --1400
	wait for 100 ns;     b0 <= '0';   b1 <= '0';   b2 <= '1';   b3 <= '0';   b4 <= '0';  --1500
	wait for 100 ns;     b0 <= '0';   b1 <= '0';   b2 <= '0';   b3 <= '0';   b4 <= '0';  --1600
	wait for 100 ns;     b0 <= '1';   b1 <= '0';   b2 <= '0';   b3 <= '1';   b4 <= '0';  --1700
	wait for 100 ns;     b0 <= '1';   b1 <= '1';   b2 <= '0';   b3 <= '0';   b4 <= '0';  --1800
	wait for 100 ns;     b0 <= '0';   b1 <= '1';   b2 <= '1';   b3 <= '0';   b4 <= '0';  --1900
	wait for 100 ns;     b0 <= '0';   b1 <= '1';   b2 <= '1';   b3 <= '1';   b4 <= '0';  --2000
	wait for 100 ns;     b0 <= '0';   b1 <= '1';   b2 <= '1';   b3 <= '1';   b4 <= '0';  --2100
	wait for 100 ns;     b0 <= '0';   b1 <= '0';   b2 <= '1';   b3 <= '1';   b4 <= '1';  --2200
	wait for 100 ns;     b0 <= '1';   b1 <= '0';   b2 <= '0';   b3 <= '0';   b4 <= '0';  --2300
	wait for 100 ns;     b0 <= '1';   b1 <= '0';   b2 <= '1';   b3 <= '0';   b4 <= '0';  --2400
	wait for 100 ns;     b0 <= '0';   b1 <= '0';   b2 <= '1';   b3 <= '0';   b4 <= '0';  --2500
	wait for 100 ns;     b0 <= '0';   b1 <= '0';   b2 <= '0';   b3 <= '1';   b4 <= '0';  --2600
	wait for 100 ns;     b0 <= '0';   b1 <= '0';   b2 <= '0';   b3 <= '0';   b4 <= '0';  --2700
	wait;															-- infinite wait
end process;
end arch;



