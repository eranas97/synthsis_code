--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

ENTITY testbench2 IS END;

------------------------------------------------------------------------
-- testbench for 8-bit adder
-- reads file "vectors" 
------------------------------------------------------------------------
LIBRARY ieee;
USE ieee.std_logic_1164.ALL;
USE std.textio.ALL;
ARCHITECTURE adder8 OF testbench2 IS 
    
    -----------------------------------
    -- component declaration for adderN
    -----------------------------------
    COMPONENT addern 
    GENERIC(n : integer);
    PORT (a    : IN std_logic_vector(n DOWNTO 1);
          b    : IN std_logic_vector(n DOWNTO 1);
          cin  : IN std_logic;
          sum  : OUT std_logic_vector(n DOWNTO 1);
          cout : OUT std_logic);
    END COMPONENT;

    -- declare one large signal
    SIGNAL ports : std_logic_vector(26 DOWNTO 1) := (OTHERS => 'Z');

    -- declare an alias for each port
    -- this makes it easier to connect the signals to the component
    ALIAS a    : std_logic_vector(8 DOWNTO 1) IS ports(26 DOWNTO 19);
    ALIAS b    : std_logic_vector(8 DOWNTO 1) IS ports(18 DOWNTO 11);
    ALIAS cin  : std_logic            IS ports(10);
    ALIAS sum  : std_logic_vector(8 DOWNTO 1) IS ports(9 DOWNTO 2);
    ALIAS cout : std_logic            IS ports(1);

BEGIN
    -- instantiate the component
    uut: addern GENERIC MAP(8)
        PORT MAP(a => a,
             b => b,
             cin => cin,
             sum => sum,
             cout => cout);
 

    -- provide stimulus and check the result
    test: PROCESS
    FILE vector_file : text IS IN "vectors";
    VARIABLE l : line;
    VARIABLE vector_time : time;
    VARIABLE r : real;
    VARIABLE good_number : boolean;
    VARIABLE signo : integer;
    BEGIN
    WHILE NOT endfile(vector_file) LOOP
        readline(vector_file, l);
        
        -- read the time from the beginning of the line
        -- skip the line if it doesn't start with a number
        read(l, r, good => good_number);
        NEXT WHEN NOT good_number;

        vector_time := r * 1 ns;        -- convert real number to time
        IF (now < vector_time) THEN     -- wait until the vector time
        WAIT FOR vector_time - now;
        END IF;

        signo := 26;

        FOR i IN l'RANGE LOOP
        CASE l(i) IS 
            WHEN '0' => -- Drive 0
                ports(signo) <= '0';
            WHEN '1' => -- Drive 1
                ports(signo) <= '1';
            WHEN 'h' | 'H' => -- Test for 1
                ASSERT ports(signo) = '1';
            WHEN 'l' | 'L' => -- Test for 0
                ASSERT ports(signo) = '0';
            WHEN 'x' | 'X' => -- Don't care
                NULL;
            WHEN ' ' | ht => -- Skip white space
                NEXT;
            WHEN OTHERS =>
                -- Illegal character
                ASSERT false
                  REPORT "Illegal character in vector file: " & l(i);
                EXIT;
        END CASE;
        signo := signo - 1;
        END LOOP;
    END LOOP;
    ASSERT false REPORT "Test complete";
    WAIT;
    END PROCESS;
END;
