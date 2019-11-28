--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

-- Test Bench

library ieee, work;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.std_logic_unsigned.all;
use std.textio.all ;
USE work.all; 

ENTITY test_ringbuf IS
END test_ringbuf;

ARCHITECTURE test_ringbuf_ARCH OF test_ringbuf IS
COMPONENT ringbuf
   GENERIC (
      counter_size : integer := 8;
      buffer_size : integer := 256
   );
   PORT (
      clock : IN std_logic;
      reset : IN std_logic;
      txda : IN std_logic;
      rxda : OUT std_logic;
      txdb : IN std_logic;
      rxdb : OUT std_logic;
      txdc : IN std_logic;
      rxdc : OUT std_logic;
      txdd : IN std_logic;
      rxdd : OUT std_logic;
      txc : OUT std_logic;
      outstrobe : OUT std_logic;
      wrb : IN std_logic;
      csb : IN std_logic;
      switch : IN std_logic_vector (3 downto 0);
      monitor_activity : out std_logic_vector(7 DOWNTO 0)
   );
END component;
SIGNAL clock : std_logic := '0';
SIGNAL reset, txda, rxda, txc	: std_logic;
SIGNAL rxdb, rxdc, rxdd	: std_logic;
SIGNAL txdb, txdc, txdd	: std_logic := '0';
SIGNAL addrs : std_logic_vector(15 DOWNTO 0);
SIGNAL pseudo : std_logic_vector(19 DOWNTO 0);
SIGNAL storage : std_logic_vector(19 DOWNTO 0);
SIGNAL expected, outstrobe, actual, dataerror : std_logic;
SIGNAL wrb : std_logic := '0';
SIGNAL csb : std_logic := '1';
SIGNAL switch : std_logic_vector (3 downto 0) := "0000";
SIGNAL test1 : boolean := true;
SIGNAL monitor_activity : std_logic_vector(7 DOWNTO 0);

BEGIN

Switch_Data : PROCESS
  variable line_in: Line;
  variable test : boolean;
  file f: TEXT is in "which_test.txt";
BEGIN
   readline(f, line_in);
   read (line_in, test);
   wrb <= '0';
   csb <= '1';
   switch <= "0000";
   IF test = true THEN
     FOR data_value IN 0 TO 11 LOOP
        switch <= conv_std_logic_vector(data_value,4);
        WAIT FOR 100 NS;
        wrb	 <= '0';
        csb    <= '0';
        WAIT FOR 100 NS;
        wrb	 <= '1';
        WAIT FOR 200 NS;
        WAIT FOR 200000 NS;
     END LOOP;
   END IF;
   WAIT;
END PROCESS;

Gen_Reset : PROCESS
BEGIN
   reset	 <= '0';
   WAIT FOR 400 NS;
   reset	 <= '1';
   WAIT FOR 1000000 NS;
   WAIT;
END PROCESS;

Gen_Clock : PROCESS
BEGIN
   FOR a IN 0 TO 8000000 LOOP
      WAIT FOR 100 NS;
      clock	 <= '0';
      WAIT FOR 100 NS;
      clock	 <= '1';
   END LOOP;
WAIT;
END PROCESS;

Generate_Data : PROCESS (txc, reset)
BEGIN
  IF reset = '0' THEN
    pseudo <= "00000000000000000000";
  ELSIF (txc'event AND txc = '1') THEN
    pseudo <= pseudo(18 DOWNTO 0) & NOT (pseudo(2) XOR pseudo(19));
  END IF;
END PROCESS;

-- Assigns the output from the LFSR to the transmit data input
-- into the device
txda <= pseudo(19);

-- This section puts the data that comes out of the ring buf into
-- a LFSR with the same taps as the generated data. It then compares
-- this data with the next bit to ensure that the data is correct.
Compare_Data : PROCESS (clock)
BEGIN
  IF (clock'event AND clock = '0') THEN
    IF reset = '0' THEN
      storage <= "00000000000000000000";
      expected <= '0';
    ELSE
      IF outstrobe = '1' THEN
        storage <= storage(18 DOWNTO 0) & rxda;
        expected <= NOT (storage(2) XOR storage(19));
      END IF;
    END IF;
  END IF;
END PROCESS;

actual <= storage(0);

Produce_Error_Sig : PROCESS (clock)
BEGIN
  IF (clock'event AND clock = '1') THEN
    IF reset = '0' THEN
      dataerror <= '0';
    ELSE
      dataerror <= NOT (actual XOR expected);
    END IF;
  END IF;
END PROCESS;

print_error : PROCESS (dataerror)
  variable line_out: Line;
BEGIN
  IF (dataerror'event AND dataerror = '0') THEN
    write (line_out,string'("** ERROR ** at ") ); 
    write (line_out, now ); 
    write (line_out,string'(": Data Errored Value not Expected.") ); 
    writeline(OUTPUT, line_out);
  END IF;
END PROCESS;

print_restore : PROCESS (dataerror)
  variable line_out: Line;
BEGIN
  IF (dataerror'event AND dataerror = '1') THEN
    write (line_out,string'("** RESTORED ** at ") ); 
    write (line_out, now ); 
    write (line_out,string'(": Data Returned to Expected Value.") ); 
    writeline(OUTPUT, line_out);
  END IF;
END PROCESS;

rxd_activity : PROCESS (rxda,rxdb,rxdc,rxdd)
  variable line_out: Line;
BEGIN
  IF (rxda'event AND rxda = '0'AND rxda'last_value = '1') THEN
    write (line_out,string'("** RXDA Mark ** at ") ); 
    write (line_out, now );
    write (line_out,string'(" Primary Channel") );  
    writeline(OUTPUT, line_out);
  END IF;
  IF (rxdb'event AND rxdb = '0'AND rxdb'last_value = '1') THEN
    write (line_out,string'("** RXDB Mark ** at ") ); 
    write (line_out, now ); 
    writeline(OUTPUT, line_out);
  END IF;
  IF (rxdc'event AND rxdc = '0'AND rxdc'last_value = '1') THEN
    write (line_out,string'("** RXDC Mark ** at ") ); 
    write (line_out, now ); 
    writeline(OUTPUT, line_out);
  END IF;
  IF (rxdd'event AND rxdd = '0'AND rxdd'last_value = '1') THEN
    write (line_out,string'("** RXDD Mark ** at ") ); 
    write (line_out, now ); 
    writeline(OUTPUT, line_out);
  END IF;
END PROCESS;

ring_INST: ringbuf
   GENERIC MAP (
      counter_size => 6,
      buffer_size  => 64
   )
	PORT MAP (
   clock => clock,
   reset => reset,
   txda => txda,
   rxda => rxda,
   txdb => txdb,
   rxdb => rxdb,
   txdc => txdc,
   rxdc => rxdc,
   txdd => txdd,
   rxdd => rxdd,
   txc => txc,
   outstrobe => outstrobe,
   wrb => wrb,
   csb => csb,
   switch => switch,
   monitor_activity => monitor_activity
);

END test_ringbuf_ARCH;

