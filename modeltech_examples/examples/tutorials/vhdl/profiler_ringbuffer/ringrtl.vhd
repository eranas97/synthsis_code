--
-- Copyright 1991-2016 Mentor Graphics Corporation
--
-- All Rights Reserved.
--
-- THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
-- MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
--   

-- Top Level

library ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;

ENTITY ringbuf IS
   GENERIC (
      counter_size : integer := 6;
      buffer_size : integer := 64
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
END ringbuf;

ARCHITECTURE RTL OF ringbuf IS

COMPONENT store
   GENERIC (
      counter_size : integer := 4;
      buffer_size : integer := 16
   );
   PORT (
      clock	: IN std_logic;
      reset	: IN std_logic;
      oeenable : IN std_logic;
      txda : IN std_logic;
      ramadrs : IN std_logic_vector((counter_size *2) DOWNTO 0);
      buffers : OUT std_logic_vector((buffer_size-1) DOWNTO 0)
   );
END component;

component control
   GENERIC (
      counter_size : integer := 4
   );
   PORT (
      clock : IN std_logic;
      reset : IN std_logic;
      ramadrs : OUT std_logic_vector((counter_size * 2) DOWNTO 0);
      oeenable : OUT std_logic;
      outstrobe : OUT std_logic;
      txc : OUT std_logic;
      wrb : in std_logic;
      csb : in std_logic;
      switch : in std_logic_vector(3 DOWNTO 0);
      txd : in std_logic_vector(3 DOWNTO 0);
      buffer_txd : out std_logic;
      rxd : out std_logic_vector(3 DOWNTO 0);
      buffer_rxd : in std_logic;
      monitor_activity : out std_logic_vector(7 DOWNTO 0)
   );
END component;

component retrieve
   GENERIC (
      counter_size : integer := 4;
      buffer_size : integer := 16
   );
   PORT (
      outstrobe : IN std_logic;
      ramadrs : IN std_logic_vector((counter_size * 2) DOWNTO 0);
      buffers : IN std_logic_vector((buffer_size -1) DOWNTO 0);
      rxda : OUT std_logic
   );
END component;

signal ramadrs : std_logic_vector((counter_size * 2) DOWNTO 0);
signal oeenable : std_logic;
signal outstrobe_int : std_logic;
signal buffers : std_logic_vector((buffer_size -1) DOWNTO 0);
signal rxd_int :std_logic;
signal txd_int :std_logic;
signal txd : std_logic_vector(3 DOWNTO 0);
signal rxd : std_logic_vector(3 DOWNTO 0);

BEGIN

txd <= txdd & txdc & txdb & txda;
rxda <= rxd(3);
rxdb <= rxd(2);
rxdc <= rxd(1);
rxdd <= rxd(0);

block1_INST: store
   GENERIC MAP(
      counter_size => counter_size,
      buffer_size => buffer_size
   )
   PORT MAP (
      clock	=> clock,
      reset	=> reset,
      oeenable => oeenable,
      txda => txd_int,
      ramadrs => ramadrs,
      buffers => buffers
   );

block2_INST: control
   GENERIC MAP (
      counter_size => counter_size
   )
   PORT MAP (
      clock	=> clock,
      reset	=> reset,
      ramadrs => ramadrs,
      oeenable => oeenable,
      outstrobe => outstrobe_int,
      txc => txc,
      wrb => wrb,
      csb => csb,
      switch => switch,
      txd => txd,
      buffer_txd => txd_int,
      rxd => rxd,
      buffer_rxd => rxd_int,
      monitor_activity => monitor_activity
   );

block3_INST: retrieve
   GENERIC MAP (
      counter_size => counter_size,
      buffer_size => buffer_size
   )
   PORT MAP (
      outstrobe => outstrobe_int,
      ramadrs => ramadrs,
      buffers => buffers,
      rxda => rxd_int
   );

outstrobe <= outstrobe_int;

END RTL;


