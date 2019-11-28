library ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.std_logic_unsigned.all;

ENTITY mode_two_control IS
   PORT (
      clock	: IN    std_logic;
      reset	: IN    std_logic;
      txc_128k	: IN    std_logic;
      mode	: IN    std_logic_vector(1 DOWNTO 0);
      bit_strobe	: IN    std_logic;
      slot_strobe	: IN    std_logic;
      overhead	: IN    std_logic;
      data_strobe	: OUT   std_logic;
      txc	: OUT  std_logic;
      strobe_126k	: OUT   std_logic;
      mode1_rxd	: IN    std_logic;
      mode2_rxd	: IN    std_logic;
      rxd	: OUT   std_logic;
      strobe_128k	: IN    std_logic;
      strobe_126kf	: OUT   std_logic
   );
END mode_two_control;

ARCHITECTURE RTL OF mode_two_control IS
SIGNAL data_strobe_tmp	: std_logic;
SIGNAL txc_tmp	: std_logic;
SIGNAL strobe_126k_tmp	: std_logic;
SIGNAL rxd_tmp	: std_logic;
SIGNAL strobe_126kf_tmp	: std_logic;
SIGNAL first_stage	: std_logic_vector(6 DOWNTO 0);
SIGNAL second_stage	: std_logic_vector(5 DOWNTO 0);
SIGNAL txc126a	: std_logic;
SIGNAL txc126b	: std_logic;
SIGNAL txc_126k	: std_logic;
SIGNAL txc_128kr	: std_logic;
SIGNAL txc_126kr	: std_logic;
SIGNAL mode1_rxdr	: std_logic;
SIGNAL mode2_rxdr	: std_logic;
SIGNAL strobe_126_edge	: std_logic;
SIGNAL Z_0_mode2_rxdr	: std_logic;
SIGNAL Z_0_txc_126kr	: std_logic;
SIGNAL Z_0_mode1_rxdr	: std_logic;
SIGNAL Z_0_txc_128kr	: std_logic;
SIGNAL Z_0_txc_126k	: std_logic;
SIGNAL Z_0_txc126b	: std_logic;
SIGNAL Z_0_txc126a	: std_logic;
SIGNAL Z_0_second_stage	: std_logic_vector(5 DOWNTO 0);
SIGNAL Z_0_first_stage	: std_logic_vector(6 DOWNTO 0);

BEGIN

data_strobe	<= data_strobe_tmp;
txc	<= txc_tmp;
strobe_126k	<= strobe_126k_tmp;
rxd	<= rxd_tmp;
strobe_126kf	<= strobe_126kf_tmp;
mode2_rxdr	 <= Z_0_mode2_rxdr;
txc_126kr	 <= Z_0_txc_126kr;
mode1_rxdr	 <= Z_0_mode1_rxdr;
txc_128kr	 <= Z_0_txc_128kr;
txc_126k	 <= Z_0_txc_126k;
txc126b	 <= Z_0_txc126b;
txc126a	 <= Z_0_txc126a;
second_stage	 <= Z_0_second_stage;
first_stage	 <= Z_0_first_stage;
PROCESS (clock)
BEGIN
IF clock'event AND clock = '1'  THEN
   IF reset = '0' THEN
      Z_0_first_stage	 <= "0000000";
      Z_0_second_stage	 <= "000000";
      Z_0_txc126a	 <= '0';
      Z_0_txc126b	 <= '0';
      Z_0_txc_126k	 <= '0';
   ELSE
      Z_0_first_stage	 <= first_stage + "0111111";
      Z_0_second_stage	 <= second_stage + (first_stage(6) XOR second_stage(0));
      Z_0_txc126a	 <= second_stage(5);
      Z_0_txc126b	 <= NOT txc126a;
      Z_0_txc_126k	 <= NOT second_stage(5);
   END IF;
   IF reset = '0' THEN
      Z_0_txc_128kr	 <= '0';
   ELSE
      IF strobe_128k = '1' THEN
         Z_0_txc_128kr	 <= txc_128k;
      END IF;
   END IF;
   IF reset = '0' THEN
      Z_0_mode1_rxdr	 <= '0';
   ELSE
      IF (strobe_128k AND NOT txc_128k) = '1' THEN
         Z_0_mode1_rxdr	 <= mode1_rxd;
      END IF;
   END IF;
   IF reset = '0' THEN
      Z_0_txc_126kr	 <= '0';
   ELSE
      IF strobe_126_edge = '1' THEN
         Z_0_txc_126kr	 <= txc_126k;
      END IF;
   END IF;
   IF reset = '0' THEN
      Z_0_mode2_rxdr	 <= '0';
   ELSE
      IF (strobe_126_edge AND txc_126kr) = '1' THEN
         Z_0_mode2_rxdr	 <= mode2_rxd;
      END IF;
   END IF;
END IF;
END PROCESS;

strobe_126k_tmp	 <= NOT (txc126a OR txc126b);
strobe_126kf_tmp	 <= strobe_126_edge AND txc_126kr;
strobe_126_edge	 <= NOT (txc126a XOR txc126b);
txc_tmp <= txc_128kr WHEN (mode = "00" OR mode = "01") ELSE txc_126kr;
rxd_tmp <= mode1_rxdr WHEN (mode = "00" OR mode = "01") ELSE mode2_rxdr;
data_strobe_tmp	 <= bit_strobe AND slot_strobe AND NOT overhead;
END RTL;


