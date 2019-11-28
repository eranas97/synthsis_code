library ieee;
USE ieee.std_logic_1164.all;
USE ieee.std_logic_arith.all;
USE ieee.std_logic_unsigned.all;

ENTITY micro IS
   PORT (
      address	: IN    std_logic_vector(  3 DOWNTO 0);
      data_in	: IN    std_logic_vector(7 DOWNTO 0);
      data_out	: OUT   std_logic_vector(7 DOWNTO 0);
      rd	: IN    std_logic;
      wr	: IN    std_logic;
      cs	: IN       std_logic;
      reset	: IN    std_logic;
      tri_state	: OUT   std_logic;
      crc_enable	: OUT   std_logic;
      test_mode	: OUT   std_logic;
      add_channel	: OUT   std_logic;
      state_control	: OUT   std_logic_vector(1 DOWNTO 0);
      mode_control	: OUT   std_logic_vector(1 DOWNTO 0);
      fifo_reset	: OUT   std_logic;
      int_ack	: OUT   std_logic;
      chanenb	: OUT   std_logic_vector(4 DOWNTO 0);
      group_id	: OUT   std_logic_vector(5 DOWNTO 0);
      variable_rst	: OUT   std_logic;
      data_mode	: OUT   std_logic;
      clam_data	: OUT   std_logic;
      search	: OUT   std_logic;
      swap_channel	: OUT   std_logic;
      swap_byte	: OUT   std_logic;
      tx_pattern	: OUT   std_logic;
      gid_error	: IN    std_logic;
      in_sync	: IN   std_logic;
      emp_flag	: IN    std_logic;
      full_flag	: IN    std_logic;
      pointer	: IN    std_logic_vector(13 DOWNTO 0);
      master_cid_sync	: IN    std_logic;
      master_frame_sync	: IN    std_logic;
      nand_tree	: OUT   std_logic;
      crc_tri_state	: IN  std_logic;
      var_tri_state	: IN    std_logic;
      fs_tri_state	: IN    std_logic;
      open_collector	: IN    std_logic;
      fifo_test	: OUT   std_logic
   );
END micro;

ARCHITECTURE RTL OF micro IS
SIGNAL data_out_tmp	: std_logic_vector(7 DOWNTO 0);
SIGNAL tri_state_tmp	: std_logic;
SIGNAL crc_enable_tmp	: std_logic;
SIGNAL test_mode_tmp	: std_logic;
SIGNAL add_channel_tmp	: std_logic;
SIGNAL state_control_tmp	: std_logic_vector(1 DOWNTO 0);
SIGNAL mode_control_tmp	: std_logic_vector(1 DOWNTO 0);
SIGNAL fifo_reset_tmp	: std_logic;
SIGNAL int_ack_tmp	: std_logic;
SIGNAL chanenb_tmp	: std_logic_vector(4 DOWNTO 0);
SIGNAL group_id_tmp	: std_logic_vector(5 DOWNTO 0);
SIGNAL variable_rst_tmp	: std_logic;
SIGNAL data_mode_tmp	: std_logic;
SIGNAL clam_data_tmp	: std_logic;
SIGNAL search_tmp	: std_logic;
SIGNAL swap_channel_tmp	: std_logic;
SIGNAL swap_byte_tmp	: std_logic;
SIGNAL tx_pattern_tmp	: std_logic;
SIGNAL nand_tree_tmp	: std_logic;
SIGNAL fifo_test_tmp	: std_logic;
SIGNAL reg0	: std_logic_vector(7 DOWNTO 0);
SIGNAL reg2	: std_logic_vector(6 DOWNTO 0);
SIGNAL reg4	: std_logic_vector(5 DOWNTO 0);
SIGNAL reg5	: std_logic_vector(7 DOWNTO 0);
SIGNAL register_tri_state	: std_logic;
SIGNAL Z_0_reg5	: std_logic_vector(7 DOWNTO 0);
SIGNAL Z_0_reg4	: std_logic_vector(5 DOWNTO 0);
SIGNAL Z_0_reg2	: std_logic_vector(6 DOWNTO 0);
SIGNAL Z_0_reg0	: std_logic_vector(7 DOWNTO 0);
SIGNAL Z_0_data_out	: std_logic_vector(7 DOWNTO 0);
SIGNAL Z_0_register_tri_state	: std_logic;

BEGIN

data_out	<= data_out_tmp;
tri_state	<= tri_state_tmp;
crc_enable	<= crc_enable_tmp;
test_mode	<= test_mode_tmp;
add_channel	<= add_channel_tmp;
state_control	<= state_control_tmp;
mode_control	<= mode_control_tmp;
fifo_reset	<= fifo_reset_tmp;
int_ack	<= int_ack_tmp;
chanenb	<= chanenb_tmp;
group_id	<= group_id_tmp;
variable_rst	<= variable_rst_tmp;
data_mode	<= data_mode_tmp;
clam_data	<= clam_data_tmp;
search	<= search_tmp;
swap_channel	<= swap_channel_tmp;
swap_byte	<= swap_byte_tmp;
tx_pattern	<= tx_pattern_tmp;
nand_tree	<= nand_tree_tmp;
fifo_test	<= fifo_test_tmp;
reg5	 <= Z_0_reg5;
reg4	 <= Z_0_reg4;
reg2	 <= Z_0_reg2;
reg0	 <= Z_0_reg0;
data_out_tmp	 <= Z_0_data_out;
register_tri_state	 <= Z_0_register_tri_state;
PROCESS (wr,reset)
BEGIN
IF reset = '0' THEN
   Z_0_reg0	 <= "00000000";
   Z_0_reg2	 <= "0000000";
   Z_0_reg4	 <= "000000";
   Z_0_reg5	 <= "00000000";
ELSIF wr'event AND wr = '1'  THEN
   IF cs = '0' THEN
      CASE address IS
      WHEN "0000" =>
         Z_0_reg0	 <= data_in;
      WHEN "0010" =>
         Z_0_reg2	 <= data_in(6 DOWNTO 0);
      WHEN "0100" =>
         Z_0_reg4	 <= data_in(5 DOWNTO 0);
      WHEN "0101" =>
         Z_0_reg5	 <= data_in;
      WHEN OTHERS =>
         NULL;
      END CASE;
   END IF;
END IF;
END PROCESS;

PROCESS (rd,cs,address,reg0,reg2,reg4,reg5,gid_error,in_sync,emp_flag,full_flag,
   pointer,master_cid_sync,master_frame_sync,crc_tri_state,var_tri_state,fs_tri_state
   ,register_tri_state,open_collector)
BEGIN
   IF rd = '0' AND cs = '0' THEN
      Z_0_register_tri_state	 <= '1';
   ELSE
      Z_0_register_tri_state	 <= '0';
   END IF;
   CASE address IS
   WHEN "0000" =>
      Z_0_data_out	 <= reg0;
   WHEN "0010" =>
      Z_0_data_out	 <= '0' & reg2;
   WHEN "0100" =>
      Z_0_data_out	 <= "00" & reg4;
   WHEN "0101" =>
      Z_0_data_out	 <= reg5;
   WHEN "0110" =>
      Z_0_data_out	 <= std_logic_vector'("1111" & gid_error & in_sync) & emp_flag
    & full_flag;
   WHEN "0111" =>
      Z_0_data_out	 <= pointer(7 DOWNTO 0);
   WHEN "1000" =>
      Z_0_data_out	 <= master_cid_sync & master_frame_sync & pointer(13 DOWNTO 8)
   ;
   WHEN "1001" =>
      Z_0_data_out	 <= std_logic_vector'("111" & crc_tri_state) & var_tri_state & 
   fs_tri_state & open_collector & register_tri_state;
   WHEN OTHERS =>
      Z_0_data_out	 <= "11001110";
   END CASE;
END PROCESS;

crc_enable_tmp	 <= reg0(0);
test_mode_tmp	 <= reg5(3);
add_channel_tmp <= reg0(1);
state_control_tmp	 <= reg0(3 DOWNTO 2);
mode_control_tmp	 <= reg0(5 DOWNTO 4);
fifo_reset_tmp	 <= reg0(6);
int_ack_tmp	 <= reg0(7);
chanenb_tmp	 <= reg2(4 DOWNTO 0);
nand_tree_tmp	 <= reg2(5);
fifo_test_tmp	 <= reg2(6);
group_id_tmp	 <= reg4;
variable_rst_tmp	 <= reg5(0);
data_mode_tmp	 <= reg5(1);
clam_data_tmp	 <= reg5(2);
search_tmp	 <= reg5(4);
swap_channel_tmp	 <= reg5(5);
swap_byte_tmp	 <= reg5(6);
tx_pattern_tmp	 <= reg5(7);
tri_state_tmp	 <= register_tri_state;
END RTL;
