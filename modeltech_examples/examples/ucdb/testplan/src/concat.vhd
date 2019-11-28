library ieee;
USE ieee.std_logic_1164.all;

ENTITY concat IS
   PORT (
      reset	: IN    std_logic;
      clock	: IN    std_logic;
      address	: IN    std_logic_vector(3 DOWNTO 0);
      pdata	: INOUT std_logic_vector(7 DOWNTO 0);
      rdb	: IN    std_logic;
      csb	: IN    std_logic;
      wrb	: IN    std_logic;
      crc_write	: OUT   std_logic;
      crc_read	: OUT   std_logic;
      crc_address	: OUT std_logic_vector(4 DOWNTO 0);
      crc	: INOUT std_logic_vector(3 DOWNTO 0);
      fifo_ram_data	: IN    std_logic_vector(7 DOWNTO 0);
      fifo_out_clock	: OUT   std_logic;
      fifo_full_indicate	: IN    std_logic;
      fifo_empty_indicate	: IN    std_logic;
      reset_fifo	: OUT   std_logic;
      micro_interrupt	: OUT   std_logic;
      txc	: OUT   std_logic;
      iom_sds1	: IN    std_logic;
      iom_sds2	: IN    std_logic;
      iom_dck	: IN    std_logic;
      iom_du	: OUT std_logic;
      iom_dd	: IN    std_logic;
      prescale_1m	: OUT   std_logic;
      prescale_8m	: OUT   std_logic;
      variable_address	: OUT   std_logic_vector(7 DOWNTO 0);
      variable_rdb	: OUT   std_logic;
      variable_wrb	: OUT   std_logic;
      variable_data	: INOUT std_logic_vector(7 DOWNTO 0);
      fs_data	: INOUT std_logic_vector(7 DOWNTO 0);
      fs_address	: OUT   std_logic_vector(18 DOWNTO 0);
      memcs	: IN    std_logic;
      amuxsel	: OUT   std_logic;
      fsoe	: OUT   std_logic;
      fswe	: OUT   std_logic;
      fsstr	: OUT   std_logic;
      fscs	: OUT   std_logic;
      srdy	: OUT   std_logic;
      cpfswe	: OUT   std_logic;
      cpfsrd	: OUT   std_logic;
      rxd	: OUT std_logic;
      txd	: IN std_logic
   );
END concat;

ARCHITECTURE RTL OF concat IS

component ARBITRATOR
  port (CLOCK: in STD_LOGIC;
        RESET: in STD_LOGIC;
        PRE_PROC_WR_REQUEST: in STD_LOGIC;
        POST_PROC_RD_REQUEST: in STD_LOGIC;
        CPU_WR: in STD_LOGIC;
        CPU_RD: in STD_LOGIC;
        MEMORY_CS: in STD_LOGIC;
        ADD_MUX_SEL: out STD_LOGIC;
        FRAME_STORE_OE: out STD_LOGIC;
        FRAME_STORE_WE: out STD_LOGIC;
        FRAME_STORE_STROBE: out STD_LOGIC;
        FRAME_STORE_CS: out STD_LOGIC;
        CPU_READY: out STD_LOGIC;
        CPU_FS_WE: out STD_LOGIC;
        CPU_FS_RD: out STD_LOGIC);
end component;
component FIFOCELL
  port (CLOCK: in STD_LOGIC;
        RESET: in STD_LOGIC;
        STATUS_IN: in STD_LOGIC;
        SHIFT_IN: out STD_LOGIC;
        SHIFT_OUT: in STD_LOGIC;
        STATUS_OUT: out STD_LOGIC;
        DIN: in STD_LOGIC;
        DOUT: out STD_LOGIC);
end component;
component FS_ADD_MUX
  port (A: in STD_LOGIC_VECTOR(18 downto 0);
        B: in STD_LOGIC_VECTOR(18 downto 0);
        SEL: in STD_LOGIC;
        SWITCH: out STD_LOGIC_VECTOR(18 downto 0));
end component;
component micro
   PORT (
      address	: IN    std_logic_vector(3 DOWNTO 0);
      data_in	: IN    std_logic_vector(7 DOWNTO 0);
      data_out	: OUT   std_logic_vector(7 DOWNTO 0);
      rd	: IN    std_logic;
      wr	: IN    std_logic;
      cs	: IN    std_logic;
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
      in_sync	: IN     std_logic;
      emp_flag	: IN    std_logic;
      full_flag	: IN    std_logic;
      pointer	: IN    std_logic_vector(13 DOWNTO 0);
      master_cid_sync	: IN    std_logic;
      master_frame_sync	: IN    std_logic;
      nand_tree	: OUT   std_logic;
      crc_tri_state	: IN   std_logic;
      var_tri_state	: IN    std_logic;
      fs_tri_state	: IN    std_logic;
      open_collector	: IN    std_logic;
      fifo_test	: OUT   std_logic
   );
END component;
component PRE_PROCESSOR
  port (RESET: in STD_LOGIC;
        CLOCK: in STD_LOGIC;
        VARIABLE_ADDRESS: out STD_LOGIC_VECTOR(7 downto 0);
        VARIABLE_WRITE: out STD_LOGIC;
        VARIABLE_READ: out STD_LOGIC;
        VARIABLE_SAVE: out STD_LOGIC_VECTOR(7 downto 0);
        VARIABLE_RESTORE: in STD_LOGIC_VECTOR(7 downto 0);
        VARIABLE_RESET: in STD_LOGIC;
        DATA_MODE: in STD_LOGIC;
        FS_WRITE: out STD_LOGIC;
        FSDATENB_STROBE: out STD_LOGIC;
        FRAME_STORE_DATA: out STD_LOGIC_VECTOR(7 downto 0);
        IOM_DCK: in STD_LOGIC;
        IOM_SDS1: in STD_LOGIC;
        IOM_SDS2: in STD_LOGIC;
        ADDRESS_POINTER: out STD_LOGIC_VECTOR(13 downto 0);
        FS_ADDRESS: out STD_LOGIC_VECTOR(18 downto 0);
        IOM_DD: in STD_LOGIC;
        PRE8M: in STD_LOGIC;
        MASTER_CID_SYNC: out STD_LOGIC;
        MASTER_FRAME_SYNC: out STD_LOGIC;
        COMMON_RESET: out STD_LOGIC;
        TEST_MODE: in STD_LOGIC;
        GROUP_ID: in STD_LOGIC_VECTOR(5 downto 0);
        GROUP_ID_ERROR: out STD_LOGIC);
end component;
component mode_two_control
   PORT (
      clock	: IN    std_logic;
      reset	: IN    
   std_logic;
      txc_128k	: IN    std_logic;
      mode	: IN    std_logic_vector(1 DOWNTO 0);
      bit_strobe	: IN    std_logic;
      slot_strobe	: IN    std_logic;
      overhead	: IN    std_logic;
      data_strobe	: OUT   std_logic;
      txc	: OUT   
   std_logic;
      strobe_126k	: OUT   std_logic;
      mode1_rxd	: IN    std_logic;
      mode2_rxd	: IN    std_logic;
      rxd	: OUT   std_logic;
      strobe_128k	: IN    std_logic;
      strobe_126kf	: OUT   std_logic
   );
END component;
component TX_PROCESS
  port (RESET: in STD_LOGIC;
        CLOCK: in STD_LOGIC;
        CRC_WRITE: out STD_LOGIC;
        CRC_READ: out STD_LOGIC;
        VARIABLE_ADDRESS: out STD_LOGIC_VECTOR(4 downto 0);
        STATE_CONTROL: in STD_LOGIC_VECTOR(1 downto 0);
        MODE_CONTROL: in STD_LOGIC_VECTOR(1 downto 0);
        CHAN_ADD_BIT: in STD_LOGIC;
        TEST_MODE: in STD_LOGIC;
        CHANENB: in STD_LOGIC_VECTOR(4 downto 0);
        FIFO_RAM_DATA: in STD_LOGIC_VECTOR(7 downto 0);
        FIFO_FULL_INDICATE: in STD_LOGIC;
        FIFO_OUT_CLOCK: out STD_LOGIC;
        MICRO_INTERRUPT: out STD_LOGIC;
        CRC_IN: in STD_LOGIC_VECTOR(3 downto 0);
        CRC_OUT: out STD_LOGIC_VECTOR(3 downto 0);
        CRC_ENABLE: in STD_LOGIC;
        TXD: in STD_LOGIC;
        TXC: out STD_LOGIC;
        IOM_SDS1: in STD_LOGIC;
        IOM_SDS2: in STD_LOGIC;
        PRES1M: out STD_LOGIC;
        PRES8M: out STD_LOGIC;
        SWAP_CHAN: in STD_LOGIC;
        SWAP_BYTE: in STD_LOGIC;
        TX_PATTERN: in STD_LOGIC;
        IOM_DCK: in STD_LOGIC;
        IOM_DU: out STD_LOGIC;
        OPEN_COLLECTOR: out STD_LOGIC;
        NOT_CRC_READ: out STD_LOGIC;
        RESET_FIFO: in STD_LOGIC;
        FIFO_RESET: out STD_LOGIC;
        INT_ACK: in STD_LOGIC;
        DATA_STROBE: out STD_LOGIC;
        SLOT_WINDOW: out STD_LOGIC;
        OVERHEAD_OCTET: out STD_LOGIC;
        BUFFER_IN: in STD_LOGIC);

end component;
component POST_PROCESSOR
  port (CLOCK: in STD_LOGIC;
        RESET: in STD_LOGIC;
        POINTER: in STD_LOGIC_VECTOR(13 downto 0);
        FS_DATA: in STD_LOGIC_VECTOR(7 downto 0);
        FS_ADDR: out STD_LOGIC_VECTOR(18 downto 0);
        FS_READ: out STD_LOGIC;
        FS_MUX: out STD_LOGIC;
        COMMON_RST: in STD_LOGIC;
        RXD: out STD_LOGIC;
        DISABLE_SCRAM: in STD_LOGIC;
        IN_SYNC: out STD_LOGIC;
        TEST_MODE: in STD_LOGIC;
        BUFFER_SHIFT_IN: out STD_LOGIC;
        BUFFER_DATA_OUT: out STD_LOGIC; 
        TXC: in STD_LOGIC;
        STROBE_128K: out STD_LOGIC);
end component;
component schmitt
   PORT (
      a	: IN    std_logic;
      pi	: IN    std_logic;
      Z	: OUT   std_logic;
      po	: OUT   
   std_logic
   );
END component;
component bd4st
   PORT (
      a	: IN    std_logic;
      en	: IN    std_logic;
      tn	: IN    std_logic;
      pi	: IN    std_logic;
      io	: INOUT std_logic;
      zi	: OUT   std_logic;
      po	: OUT   std_logic
   );
END component;
component bt4r
   PORT (
      a	: IN    std_logic;
      en	: IN    std_logic;
      tn	: IN    std_logic;
      Z	: OUT   std_logic
   );
END component;
         
SIGNAL micro_tri_state	: std_logic;
SIGNAL crc_enable	: std_logic;
SIGNAL test_mode	: std_logic;
SIGNAL add_channel	: std_logic;
SIGNAL state_control	: std_logic_vector(1 DOWNTO 0);
SIGNAL mode_control	: std_logic_vector(1 DOWNTO 0);
SIGNAL fifo_reset	: std_logic;
SIGNAL int_ack	: std_logic;
SIGNAL chanenb	: std_logic_vector(4 DOWNTO 0);
SIGNAL variable_rst	: std_logic;
SIGNAL data_mode	: std_logic;
SIGNAL clam_data	: std_logic;
SIGNAL search	: std_logic;
SIGNAL swap_channel	: std_logic;
SIGNAL swap_byte	: std_logic;
SIGNAL tx_pattern	: std_logic;
SIGNAL crc_tri_state	: std_logic;
SIGNAL in_sync	: std_logic;
SIGNAL pre_proc_wr_request	: std_logic;
SIGNAL fsdatenb_strobe	: std_logic;
SIGNAL master_cid_sync	: std_logic;
SIGNAL master_frame_sync	: std_logic;
SIGNAL address_pointer	: std_logic_vector(13 DOWNTO 0);
SIGNAL post_proc_rd_request	: std_logic;
SIGNAL fs_mux	: std_logic;
SIGNAL preproc_fs_addr	: std_logic_vector(18 DOWNTO 0);
SIGNAL postproc_fs_addr	: std_logic_vector(18 DOWNTO 0);
SIGNAL common_reset	: std_logic;
SIGNAL open_collector	: std_logic;
SIGNAL open_collector_nt	: std_logic;
SIGNAL group_id	: std_logic_vector(5 DOWNTO 0);
SIGNAL gid_error	: std_logic;
SIGNAL txstatus_in	: std_logic_vector(31 DOWNTO 0);
SIGNAL txstatus_out	: std_logic_vector(31 DOWNTO 0);
SIGNAL txshifto	: std_logic_vector(31 DOWNTO 0);
SIGNAL txshifti	: std_logic_vector(31 DOWNTO 0);
SIGNAL txdout	: std_logic_vector(31 DOWNTO 0);
SIGNAL txdin	: std_logic_vector(31 DOWNTO 0);
SIGNAL txc_128k	: std_logic;
SIGNAL tx_shift_out	: std_logic;
SIGNAL strobe_126k	: std_logic;
SIGNAL data_strobe	: std_logic;
SIGNAL slot_window	: std_logic;
SIGNAL overhead_octet	: std_logic;
SIGNAL buffer_shift_in	: std_logic;
SIGNAL buffer_data_out	: std_logic;
SIGNAL strobe_126kf	: std_logic;
SIGNAL rxstatus_in	: std_logic_vector(31 DOWNTO 0);
SIGNAL rxstatus_out	: std_logic_vector(31 DOWNTO 0);
SIGNAL rxshifto	: std_logic_vector(31 DOWNTO 0);
SIGNAL rxshifti	: std_logic_vector(31 DOWNTO 0);
SIGNAL rxdout	: std_logic_vector(31 DOWNTO 0);
SIGNAL rxdin	: std_logic_vector(31 DOWNTO 0);
SIGNAL prerxd	: std_logic;
SIGNAL post_rxd	: std_logic;
SIGNAL strobe_128k	: std_logic;
SIGNAL reseti	: std_logic;
SIGNAL clocki	: std_logic;
SIGNAL addressi	: std_logic_vector(3 DOWNTO 0);
SIGNAL datai	: std_logic_vector(7 DOWNTO 0);
SIGNAL datao	: std_logic_vector(7 DOWNTO 0);
SIGNAL rdbi	: std_logic;
SIGNAL csbi	: std_logic;
SIGNAL wrbi	: std_logic;
SIGNAL crc_writeo	: std_logic;
SIGNAL crc_reado	: std_logic;
SIGNAL crc_addresso	: std_logic_vector(4 DOWNTO 0);
SIGNAL crci	: std_logic_vector(3 DOWNTO 0);
SIGNAL crci_clamp	: std_logic_vector(3 DOWNTO 0);
SIGNAL crco	: std_logic_vector(3 DOWNTO 0);
SIGNAL crco_clamp	: std_logic_vector(3 DOWNTO 0);
SIGNAL fifo_ram_datai	: std_logic_vector(7 DOWNTO 0);
SIGNAL fifo_out_clocko	: std_logic;
SIGNAL fifo_full_indicatei	: std_logic;
SIGNAL fifo_empty_indicatei	: std_logic;
SIGNAL reset_fifoo	: std_logic;
SIGNAL txco	: std_logic;
SIGNAL iom_sds1i	: std_logic;
SIGNAL iom_sds2i	: std_logic;
SIGNAL iom_dcki	: std_logic;
SIGNAL iom_duo	: std_logic;
SIGNAL iom_ddi	: std_logic;
SIGNAL prescale_1mo	: std_logic;
SIGNAL prescale_8mo	: std_logic;
SIGNAL variable_addresso	: std_logic_vector(7 DOWNTO 0);
SIGNAL variable_rdbo	: std_logic;
SIGNAL variable_wrbo	: std_logic;
SIGNAL variable_datao	: std_logic_vector(7 DOWNTO 0);
SIGNAL variable_datai	: std_logic_vector(7 DOWNTO 0);
SIGNAL variable_restore	: std_logic_vector(7 DOWNTO 0);
SIGNAL fs_datai	: std_logic_vector(7 DOWNTO 0);
SIGNAL fs_datao	: std_logic_vector(7 DOWNTO 0);
SIGNAL fs_addresso	: std_logic_vector(18 DOWNTO 0);
SIGNAL memcsi	: std_logic;
SIGNAL amuxselo	: std_logic;
SIGNAL fsoeo	: std_logic;
SIGNAL fsweo	: std_logic;
SIGNAL fsstro	: std_logic;
SIGNAL fscso	: std_logic;
SIGNAL srdyo	: std_logic;
SIGNAL cpfsweo	: std_logic;
SIGNAL cpfsrdo	: std_logic;
SIGNAL rxdo	: std_logic;
SIGNAL txdi	: std_logic;
SIGNAL micro_interrupto	: std_logic;
SIGNAL ntree_enb	: std_logic;
SIGNAL ntree_enbn	: std_logic;
SIGNAL csb_nand_tree	: std_logic;
SIGNAL rdb_nand_tree	: std_logic;
SIGNAL wrb_nand_tree	: std_logic;
SIGNAL tree00	: std_logic;
SIGNAL tree01	: std_logic;
SIGNAL tree02	: std_logic;
SIGNAL tree03	: std_logic;
SIGNAL tree04	: std_logic;
SIGNAL tree05	: std_logic;
SIGNAL tree06	: std_logic;
SIGNAL tree07	: std_logic;
SIGNAL tree08	: std_logic;
SIGNAL tree09	: std_logic;
SIGNAL tree10	: std_logic;
SIGNAL tree11	: std_logic;
SIGNAL tree12	: std_logic;
SIGNAL tree13	: std_logic;
SIGNAL tree14	: std_logic;
SIGNAL tree15	: std_logic;
SIGNAL tree16	: std_logic;
SIGNAL tree17	: std_logic;
SIGNAL tree18	: std_logic;
SIGNAL tree19	: std_logic;
SIGNAL tree20	: std_logic;
SIGNAL tree21	: std_logic;
SIGNAL tree22	: std_logic;
SIGNAL tree23	: std_logic;
SIGNAL tree24	: std_logic;
SIGNAL tree25	: std_logic;
SIGNAL tree26	: std_logic;
SIGNAL tree27	: std_logic;
SIGNAL tree28	: std_logic;
SIGNAL tree29	: std_logic;
SIGNAL tree30	: std_logic;
SIGNAL tree31	: std_logic;
SIGNAL tree32	: std_logic;
SIGNAL tree33	: std_logic;
SIGNAL tree34	: std_logic;
SIGNAL tree35	: std_logic;
SIGNAL tree36	: std_logic;
SIGNAL tree37	: std_logic;
SIGNAL tree38	: std_logic;
SIGNAL tree39	: std_logic;
SIGNAL tree40	: std_logic;
SIGNAL tree41	: std_logic;
SIGNAL tree42	: std_logic;
SIGNAL tree43	: std_logic;
SIGNAL tree44	: std_logic;
SIGNAL tree45	: std_logic;
SIGNAL tree46	: std_logic;
SIGNAL tree47	: std_logic;
SIGNAL tree48	: std_logic;
SIGNAL tree49	: std_logic;
SIGNAL tree50	: std_logic;
SIGNAL tree51	: std_logic;
SIGNAL end_ntree	: std_logic;
SIGNAL end_ntreen	: std_logic;
SIGNAL vcc	: std_logic;
SIGNAL crc_wrb_nt	: std_logic;
SIGNAL crc_rdb_nt	: std_logic;
SIGNAL crc_add0_nt	: std_logic;
SIGNAL crc_add1_nt	: std_logic;
SIGNAL crc_add2_nt	: std_logic;
SIGNAL crc_add3_nt	: std_logic;
SIGNAL crc_add4_nt	: std_logic;
SIGNAL fifo_out_clk_nt	: std_logic;
SIGNAL reset_fifo_nt	: std_logic;
SIGNAL micro_inter_nt	: std_logic;
SIGNAL txco_nt	: std_logic;
SIGNAL iom_duo_nt	: std_logic;
SIGNAL prescale_1mo_nt	: std_logic;
SIGNAL prescale_8mo_nt	: std_logic;
SIGNAL variable_add0_nt	: std_logic;
SIGNAL variable_add1_nt	: std_logic;
SIGNAL variable_add2_nt	: std_logic;
SIGNAL variable_add3_nt	: std_logic;
SIGNAL variable_add4_nt	: std_logic;
SIGNAL variable_add5_nt	: std_logic;
SIGNAL variable_add6_nt	: std_logic;
SIGNAL variable_add7_nt	: std_logic;
SIGNAL variable_rdbo_nt	: std_logic;
SIGNAL variable_wrbo_nt	: std_logic;
SIGNAL fs_add0_nt	: std_logic;
SIGNAL fs_add1_nt	: std_logic;
SIGNAL fs_add2_nt	: std_logic;
SIGNAL fs_add3_nt	: std_logic;
SIGNAL fs_add4_nt	: std_logic;
SIGNAL fs_add5_nt	: std_logic;
SIGNAL fs_add6_nt	: std_logic;
SIGNAL fs_add7_nt	: std_logic;
SIGNAL fs_add8_nt	: std_logic;
SIGNAL fs_add9_nt	: std_logic;
SIGNAL fs_add10_nt	: std_logic;
SIGNAL fs_add11_nt	: std_logic;
SIGNAL fs_add12_nt	: std_logic;
SIGNAL fs_add13_nt	: std_logic;
SIGNAL fs_add14_nt	: std_logic;
SIGNAL fs_add15_nt	: std_logic;
SIGNAL fs_add16_nt	: std_logic;
SIGNAL fs_add17_nt	: std_logic;
SIGNAL fs_add18_nt	: std_logic;
SIGNAL amuxselo_nt	: std_logic;
SIGNAL fsoeo_nt	: std_logic;
SIGNAL fsweo_nt	: std_logic;
SIGNAL fsstro_nt	: std_logic;
SIGNAL fscso_nt	: std_logic;
SIGNAL srdyo_nt	: std_logic;
SIGNAL cpfsweo_nt	: std_logic;
SIGNAL cpfsrdo_nt	: std_logic;
SIGNAL rxdo_nt	: std_logic;
SIGNAL chip_tri_state	: std_logic;
SIGNAL rshift_in	: std_logic;
SIGNAL rshift_out	: std_logic;
SIGNAL rdata_in	: std_logic;
SIGNAL tshift_in	: std_logic;
SIGNAL tshift_out	: std_logic;
SIGNAL fifo_test	: std_logic;
SIGNAL fifocell_clock   : std_logic;
BEGIN

control_INST: micro
	PORT MAP (
   address => addressi,
   data_in => datai,
   data_out => datao,
   rd => rdbi,
   wr => wrbi,
   cs => csbi,
   reset => reseti,
   tri_state => micro_tri_state,
   crc_enable => crc_enable,
   test_mode => test_mode,
   add_channel => add_channel,
   state_control => state_control,
   mode_control => mode_control,
   fifo_reset => fifo_reset,
   int_ack => int_ack,
   chanenb => chanenb,
   group_id => group_id,
   variable_rst => variable_rst,
   data_mode => data_mode,
   clam_data => clam_data,
   search => search,
   swap_channel => swap_channel,
   swap_byte => swap_byte,
   tx_pattern => tx_pattern,
   gid_error => gid_error,
   in_sync => in_sync,
   emp_flag => fifo_empty_indicatei,
   full_flag => fifo_full_indicatei,
   pointer => address_pointer,
   master_cid_sync => master_cid_sync,
   master_frame_sync => master_frame_sync,
   nand_tree => ntree_enb,
   crc_tri_state => crc_tri_state,
   var_tri_state => variable_rdbo,
   fs_tri_state => fsdatenb_strobe,
   open_collector => open_collector,
   fifo_test => fifo_test
);

txproc_INST: tx_process
	PORT MAP (
   reset => reseti,
   clock => clocki,
   crc_write => crc_writeo,
   crc_read => crc_reado,
   variable_address => crc_addresso,
   state_control => state_control,
   mode_control => mode_control,
   chan_add_bit => add_channel,
   test_mode => test_mode,
   chanenb => chanenb,
   fifo_ram_data => fifo_ram_datai,
   fifo_full_indicate => fifo_full_indicatei,
   fifo_out_clock => fifo_out_clocko,
   micro_interrupt => micro_interrupto,
   crc_in => crci_clamp,
   crc_out => crco_clamp,
   crc_enable => crc_enable,
   txd => txdi,
   txc => txc_128k,
   iom_sds1 => iom_sds1i,
   iom_sds2 => iom_sds2i,
   pres1m => prescale_1mo,
   pres8m => prescale_8mo,
   swap_chan => swap_channel,
   swap_byte => swap_byte,
   tx_pattern => tx_pattern,
   iom_dck => iom_dcki,
   iom_du => iom_duo,
   open_collector => open_collector,
   not_crc_read => crc_tri_state,
   reset_fifo => fifo_reset,
   fifo_reset => reset_fifoo,
   int_ack => int_ack,
   data_strobe => data_strobe,
   slot_window => slot_window,
   overhead_octet => overhead_octet,
   buffer_in => txdout(31)
);

preproc_INST: pre_processor
	PORT MAP (
   reset => reseti,
   clock => clocki,
   variable_address => variable_addresso,
   variable_write => variable_wrbo,
   variable_read => variable_rdbo,
   variable_save => variable_datao,
   variable_restore => variable_restore,
   variable_reset => variable_rst,
   data_mode => data_mode,
   fs_write => pre_proc_wr_request,
   fsdatenb_strobe => fsdatenb_strobe,
   frame_store_data => fs_datao,
   iom_dck => iom_dcki,
   iom_sds1 => iom_sds1i,
   iom_sds2 => iom_sds2i,
   address_pointer => address_pointer,
   fs_address => preproc_fs_addr,
   iom_dd => iom_ddi,
   pre8m => prescale_8mo,
   master_cid_sync => master_cid_sync,
   master_frame_sync => master_frame_sync,
   common_reset => common_reset,
   test_mode => test_mode,
   group_id => group_id,
   group_id_error => gid_error
);

postproc_INST: post_processor
	PORT MAP (
   clock => clocki,
   reset => reseti,
   pointer => address_pointer,
   fs_data => fs_datai,
   fs_addr => postproc_fs_addr,
   fs_read => post_proc_rd_request,
   fs_mux => fs_mux,
   common_rst => common_reset,
   rxd => post_rxd,
   disable_scram => search,
   in_sync => in_sync,
   test_mode => test_mode,
   buffer_shift_in => buffer_shift_in,
   buffer_data_out => buffer_data_out,
   txc => txco,
   strobe_128k => strobe_128k
);

fsarb_INST: arbitrator
	PORT MAP (
   clock => clocki,
   reset => reseti,
   pre_proc_wr_request => pre_proc_wr_request,
   post_proc_rd_request => post_proc_rd_request,
   cpu_wr => wrbi,
   cpu_rd => rdbi,
   memory_cs => memcsi,
   add_mux_sel => amuxselo,
   frame_store_oe => fsoeo,
   frame_store_we => fsweo,
   frame_store_strobe => fsstro,
   frame_store_cs => fscso,
   cpu_ready => srdyo,
   cpu_fs_we => cpfsweo,
   cpu_fs_rd => cpfsrdo
);

fsaddmux_INST: fs_add_mux
	PORT MAP (
   a => postproc_fs_addr,
   b => preproc_fs_addr,
   sel => fs_mux,
   switch => fs_addresso
);

control_126k_INST: mode_two_control
	PORT MAP (
   clock => clocki,
   reset => reseti,
   txc_128k => txc_128k,
   mode => mode_control,
   bit_strobe => data_strobe,
   slot_strobe => slot_window,
   overhead => overhead_octet,
   data_strobe => tx_shift_out,
   txc => txco,
   strobe_126k => strobe_126k,
   mode1_rxd => post_rxd,
   mode2_rxd => rxdout(31),
   rxd => prerxd,
   strobe_128k => strobe_128k,
   strobe_126kf => strobe_126kf
);

fifocell_clock <= '1' when mode_control(1) = '0' else CLOCKI;

GENER_TXFIFO: for I in 0 to 31 generate
  CELLTX: FIFOCELL
  port map (CLOCK => fifocell_clock,
            RESET => RESETI,
            STATUS_IN => TXSTATUS_IN(I),
            SHIFT_IN => TXSHIFTI(I),
            SHIFT_OUT => TXSHIFTO(I),
            STATUS_OUT => TXSTATUS_OUT(I),
            DIN => TXDIN(I),
            DOUT => TXDOUT(I) );
end generate GENER_TXFIFO;

GENER_RXFIFO: for I in 0 to 31 generate
  CELLRX: FIFOCELL
  port map (CLOCK => fifocell_clock,
            RESET => RESETI,
            STATUS_IN => RXSTATUS_IN(I),
            SHIFT_IN => RXSHIFTI(I),
            SHIFT_OUT => RXSHIFTO(I),
            STATUS_OUT => RXSTATUS_OUT(I),
            DIN => RXDIN(I),
            DOUT => RXDOUT(I) );
end generate GENER_RXFIFO;


rshift_in	 <= (buffer_shift_in AND NOT fifo_test) OR (fifo_ram_datai(2) AND fifo_test)
   ;
rshift_out	 <= (strobe_126kf AND NOT fifo_test) OR (fifo_ram_datai(3) AND fifo_test)
   ;
rdata_in	 <= (buffer_data_out AND NOT fifo_test) OR (fifo_ram_datai(3) AND fifo_test)
   ;
rxdo	 <= prerxd OR NOT clam_data;
rxstatus_in	 <= rxstatus_out(30 DOWNTO 0) & rshift_in;
rxshifto	 <= rshift_out & rxshifti(31 DOWNTO 1);
rxdin	 <= rxdout(30 DOWNTO 0) & rdata_in;
tshift_in	 <= (strobe_126k AND NOT fifo_test) OR (fifo_ram_datai(0) AND fifo_test)
   ;
tshift_out	 <= (tx_shift_out AND NOT fifo_test) OR (fifo_ram_datai(1) AND fifo_test)
   ;
txstatus_in	 <= txstatus_out(30 DOWNTO 0) & tshift_in;
txshifto	 <= tx_shift_out & txshifti(31 DOWNTO 1);
txdin	 <= txdout(30 DOWNTO 0) & txdi;
end_ntreen	 <= NOT end_ntree;
rdbi	 <= rdb_nand_tree OR ntree_enb;
wrbi	 <= wrb_nand_tree OR ntree_enb;
csbi	 <= csb_nand_tree OR ntree_enb;
open_collector_nt	 <= open_collector OR ntree_enb;
crc_wrb_nt	 <= (crc_writeo AND NOT ntree_enb) OR (end_ntreen AND ntree_enb);
crc_rdb_nt	 <= (crc_reado AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
crc_add0_nt	 <= (crc_addresso(0) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb)
   ;
crc_add1_nt	 <= (crc_addresso(1) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb)
   ;
crc_add2_nt	 <= (crc_addresso(2) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb)
   ;
crc_add3_nt	 <= (crc_addresso(3) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb)
   ;
crc_add4_nt	 <= (crc_addresso(4) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb)
   ;
fifo_out_clk_nt	 <= (fifo_out_clocko AND NOT ntree_enb) OR (end_ntree AND ntree_enb)
   ;
reset_fifo_nt	 <= (reset_fifoo AND NOT ntree_enb) OR (end_ntreen AND ntree_enb);
micro_inter_nt	 <= (micro_interrupto AND NOT ntree_enb) OR (end_ntree AND ntree_enb)
   ;
txco_nt	 <= (txco AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
iom_duo_nt	 <= (iom_duo AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
prescale_1mo_nt	 <= (prescale_1mo AND NOT ntree_enb) OR (end_ntree AND ntree_enb)
   ;
prescale_8mo_nt	 <= (prescale_8mo AND NOT ntree_enb) OR (end_ntree AND ntree_enb)
   ;
variable_add0_nt	 <= (variable_addresso(0) AND NOT ntree_enb) OR (end_ntreen AND 
   ntree_enb);
variable_add1_nt	 <= (variable_addresso(1) AND NOT ntree_enb) OR (end_ntreen AND 
   ntree_enb);
variable_add2_nt	 <= (variable_addresso(2) AND NOT ntree_enb) OR (end_ntreen AND 
   ntree_enb);
variable_add3_nt	 <= (variable_addresso(3) AND NOT ntree_enb) OR (end_ntree AND 
   ntree_enb);
variable_add4_nt	 <= (variable_addresso(4) AND NOT ntree_enb) OR (end_ntreen AND 
   ntree_enb);
variable_add5_nt	 <= (variable_addresso(5) AND NOT ntree_enb) OR (end_ntree AND 
   ntree_enb);
variable_add6_nt	 <= (variable_addresso(6) AND NOT ntree_enb) OR (end_ntree AND 
   ntree_enb);
variable_add7_nt	 <= (variable_addresso(7) AND NOT ntree_enb) OR (end_ntree AND 
   ntree_enb);
variable_rdbo_nt	 <= (variable_rdbo AND NOT ntree_enb) OR (end_ntree AND ntree_enb)
   ;
variable_wrbo_nt	 <= (variable_wrbo AND NOT ntree_enb) OR (end_ntree AND ntree_enb)
   ;
fs_add0_nt	 <= (fs_addresso(0) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb);
fs_add1_nt	 <= (fs_addresso(1) AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
fs_add2_nt	 <= (fs_addresso(2) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb);
fs_add3_nt	 <= (fs_addresso(3) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb);
fs_add4_nt	 <= (fs_addresso(4) AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
fs_add5_nt	 <= (fs_addresso(5) AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
fs_add6_nt	 <= (fs_addresso(6) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb);
fs_add7_nt	 <= (fs_addresso(7) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb);
fs_add8_nt	 <= (fs_addresso(8) AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
fs_add9_nt	 <= (fs_addresso(9) AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
fs_add10_nt	 <= (fs_addresso(10) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb)
   ;
fs_add11_nt	 <= (fs_addresso(11) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb)
   ;
fs_add12_nt	 <= (fs_addresso(12) AND NOT ntree_enb) OR (end_ntree AND ntree_enb)
   ;
fs_add13_nt	 <= (fs_addresso(13) AND NOT ntree_enb) OR (end_ntree AND ntree_enb)
   ;
fs_add14_nt	 <= (fs_addresso(14) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb)
   ;
fs_add15_nt	 <= (fs_addresso(15) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb)
   ;
fs_add16_nt	 <= (fs_addresso(16) AND NOT ntree_enb) OR (end_ntreen AND ntree_enb)
   ;
fs_add17_nt	 <= (fs_addresso(17) AND NOT ntree_enb) OR (end_ntree AND ntree_enb)
   ;
fs_add18_nt	 <= (fs_addresso(18) AND NOT ntree_enb) OR (end_ntree AND ntree_enb)
   ;
amuxselo_nt	 <= (amuxselo AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
fsoeo_nt	 <= (fsoeo AND NOT ntree_enb) OR (end_ntreen AND ntree_enb);
fsweo_nt	 <= (fsweo AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
fsstro_nt	 <= (fsstro AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
fscso_nt	 <= (fscso AND NOT ntree_enb) OR (end_ntreen AND ntree_enb);
srdyo_nt	 <= (srdyo AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
cpfsweo_nt	 <= (cpfsweo AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
cpfsrdo_nt	 <= (cpfsrdo AND NOT ntree_enb) OR (end_ntreen AND ntree_enb);
rxdo_nt	 <= (rxdo AND NOT ntree_enb) OR (end_ntree AND ntree_enb);
crco(0)	 <= crco_clamp(0) AND NOT variable_rst;
crco(1)	 <= crco_clamp(1) AND NOT variable_rst;
crco(2)	 <= crco_clamp(2) AND NOT variable_rst;
crco(3)	 <= crco_clamp(3) AND NOT variable_rst;
crci_clamp(0)	 <= crci(0) AND NOT variable_rst;
crci_clamp(1)	 <= crci(1) AND NOT variable_rst;
crci_clamp(2)	 <= crci(2) AND NOT variable_rst;
crci_clamp(3)	 <= crci(3) AND NOT variable_rst;
variable_restore(0)	 <= variable_datai(0) AND NOT variable_rst;
variable_restore(1)	 <= variable_datai(1) AND NOT variable_rst;
variable_restore(2)	 <= variable_datai(2) AND NOT variable_rst;
variable_restore(3)	 <= variable_datai(3) AND NOT variable_rst;
variable_restore(4)	 <= variable_datai(4) AND NOT variable_rst;
variable_restore(5)	 <= variable_datai(5) AND NOT variable_rst;
variable_restore(6)	 <= variable_datai(6) AND NOT variable_rst;
variable_restore(7)	 <= variable_datai(7) AND NOT variable_rst;
ntree_enbn	 <= reset AND NOT ntree_enb;
chip_tri_state	 <= NOT reset;
vcc	 <= '1';
in01_INST: schmitt
	PORT MAP (
   a => reset,
   pi => vcc,
   z => reseti,
   po => tree00
);

in02_INST: schmitt
	PORT MAP (
   a => clock,
   pi => reseti,
   z => clocki,
   po => tree01
);

in03_INST: schmitt
	PORT MAP (
   a => address(0),
   pi => tree01,
   z => addressi(0),
   po => tree02
);

in04_INST: schmitt
	PORT MAP (
   a => address(1),
   pi => tree02,
   z => addressi(1),
   po => tree03
);

in05_INST: schmitt
	PORT MAP (
   a => address(2),
   pi => tree03,
   z => addressi(2),
   po => tree04
);

in06_INST: schmitt
	PORT MAP (
   a => address(3),
   pi => tree04,
   z => addressi(3),
   po => tree05
);

in07_INST: schmitt
	PORT MAP (
   a => rdb,
   pi => tree05,
   z => rdb_nand_tree,
   po => tree06
);

in08_INST: schmitt
	PORT MAP (
   a => csb,
   pi => tree06,
   z => csb_nand_tree,
   po => tree07
);

in09_INST: schmitt
	PORT MAP (
   a => wrb,
   pi => tree07,
   z => wrb_nand_tree,
   po => tree08
);

in10_INST: schmitt
	PORT MAP (
   a => fifo_ram_data(0),
   pi => tree08,
   z => fifo_ram_datai(0),
   po => tree09
);

in11_INST: schmitt
	PORT MAP (
   a => fifo_ram_data(1),
   pi => tree09,
   z => fifo_ram_datai(1),
   po => tree10
);

in12_INST: schmitt
	PORT MAP (
   a => fifo_ram_data(2),
   pi => tree10,
   z => fifo_ram_datai(2),
   po => tree11
);

in13_INST: schmitt
	PORT MAP (
   a => fifo_ram_data(3),
   pi => tree11,
   z => fifo_ram_datai(3),
   po => tree12
);

in14_INST: schmitt
	PORT MAP (
   a => fifo_ram_data(4),
   pi => tree12,
   z => fifo_ram_datai(4),
   po => tree13
);

in15_INST: schmitt
	PORT MAP (
   a => fifo_ram_data(5),
   pi => tree13,
   z => fifo_ram_datai(5),
   po => tree14
);

in16_INST: schmitt
	PORT MAP (
   a => fifo_ram_data(6),
   pi => tree14,
   z => fifo_ram_datai(6),
   po => tree15
);

in17_INST: schmitt
	PORT MAP (
   a => fifo_ram_data(7),
   pi => tree15,
   z => fifo_ram_datai(7),
   po => tree16
);

in18_INST: schmitt
	PORT MAP (
   a => fifo_full_indicate,
   pi => tree16,
   z => fifo_full_indicatei,
   po => tree17
);

in19_INST: schmitt
	PORT MAP (
   a => fifo_empty_indicate,
   pi => tree17,
   z => fifo_empty_indicatei,
   po => tree18
);

in20_INST: schmitt
	PORT MAP (
   a => iom_sds1,
   pi => tree18,
   z => iom_sds1i,
   po => tree19
);

in21_INST: schmitt
	PORT MAP (
   a => iom_sds2,
   pi => tree19,
   z => iom_sds2i,
   po => tree20
);

in22_INST: schmitt
	PORT MAP (
   a => iom_dck,
   pi => tree20,
   z => iom_dcki,
   po => tree21
);

in23_INST: schmitt
	PORT MAP (
   a => iom_dd,
   pi => tree21,
   z => iom_ddi,
   po => tree22
);

in24_INST: schmitt
	PORT MAP (
   a => memcs,
   pi => tree22,
   z => memcsi,
   po => tree23
);

in25_INST: schmitt
	PORT MAP (
   a => txd,
   pi => tree23,
   z => txdi,
   po => tree24
);

bid01_INST: bd4st
	PORT MAP (
   a => datao(0),
   en => chip_tri_state,
   tn => micro_tri_state,
   pi => tree24,
   io => pdata(0),
   zi => datai(0),
   po => tree25
);

bid02_INST: bd4st
	PORT MAP (
   a => datao(1),
   en => chip_tri_state,
   tn => micro_tri_state,
   pi => tree25,
   io => pdata(1),
   zi => datai(1),
   po => tree26
);

bid03_INST: bd4st
	PORT MAP (
   a => datao(2),
   en => chip_tri_state,
   tn => micro_tri_state,
   pi => tree26,
   io => pdata(2),
   zi => datai(2),
   po => tree27
);

bid04_INST: bd4st
	PORT MAP (
   a => datao(3),
   en => chip_tri_state,
   tn => micro_tri_state,
   pi => tree27,
   io => pdata(3),
   zi => datai(3),
   po => tree28
);

bid05_INST: bd4st
	PORT MAP (
   a => datao(4),
   en => chip_tri_state,
   tn => micro_tri_state,
   pi => tree28,
   io => pdata(4),
   zi => datai(4),
   po => tree29
);

bid06_INST: bd4st
	PORT MAP (
   a => datao(5),
   en => chip_tri_state,
   tn => micro_tri_state,
   pi => tree29,
   io => pdata(5),
   zi => datai(5),
   po => tree30
);

bid07_INST: bd4st
	PORT MAP (
   a => datao(6),
   en => chip_tri_state,
   tn => micro_tri_state,
   pi => tree30,
   io => pdata(6),
   zi => datai(6),
   po => tree31
);

bid08_INST: bd4st
	PORT MAP (
   a => datao(7),
   en => chip_tri_state,
   tn => micro_tri_state,
   pi => tree31,
   io => pdata(7),
   zi => datai(7),
   po => tree32
);

bid09_INST: bd4st
	PORT MAP (
   a => crco(0),
   en => crc_tri_state,
   tn => ntree_enbn,
   pi => tree32,
   io => crc(0),
   zi => crci(0),
   po => tree33
);

bid10_INST: bd4st
	PORT MAP (
   a => crco(1),
   en => crc_tri_state,
   tn => ntree_enbn,
   pi => tree33,
   io => crc(1),
   zi => crci(1),
   po => tree34
);

bid11_INST: bd4st
	PORT MAP (
   a => crco(2),
   en => crc_tri_state,
   tn => ntree_enbn,
   pi => tree34,
   io => crc(2),
   zi => crci(2),
   po => tree35
);

bid12_INST: bd4st
	PORT MAP (
   a => crco(3),
   en => crc_tri_state,
   tn => ntree_enbn,
   pi => tree35,
   io => crc(3),
   zi => crci(3),
   po => tree36
);

bid13_INST: bd4st
	PORT MAP (
   a => variable_datao(0),
   en => chip_tri_state,
   tn => variable_rdbo,
   pi => tree36,
   io => variable_data(0),
   zi => variable_datai(0),
   po => tree37
);

bid14_INST: bd4st
	PORT MAP (
   a => variable_datao(1),
   en => chip_tri_state,
   tn => variable_rdbo,
   pi => tree37,
   io => variable_data(1),
   zi => variable_datai(1),
   po => tree38
);

bid15_INST: bd4st
	PORT MAP (
   a => variable_datao(2),
   en => chip_tri_state,
   tn => variable_rdbo,
   pi => tree38,
   io => variable_data(2),
   zi => variable_datai(2),
   po => tree39
);

bid16_INST: bd4st
	PORT MAP (
   a => variable_datao(3),
   en => chip_tri_state,
   tn => variable_rdbo,
   pi => tree39,
   io => variable_data(3),
   zi => variable_datai(3),
   po => tree40
);

bid17_INST: bd4st
	PORT MAP (
   a => variable_datao(4),
   en => chip_tri_state,
   tn => variable_rdbo,
   pi => tree40,
   io => variable_data(4),
   zi => variable_datai(4),
   po => tree41
);

bid18_INST: bd4st
	PORT MAP (
   a => variable_datao(5),
   en => chip_tri_state,
   tn => variable_rdbo,
   pi => tree41,
   io => variable_data(5),
   zi => variable_datai(5),
   po => tree42
);

bid19_INST: bd4st
	PORT MAP (
   a => variable_datao(6),
   en => chip_tri_state,
   tn => variable_rdbo,
   pi => tree42,
   io => variable_data(6),
   zi => variable_datai(6),
   po => tree43
);

bid20_INST: bd4st
	PORT MAP (
   a => variable_datao(7),
   en => chip_tri_state,
   tn => variable_rdbo,
   pi => tree43,
   io => variable_data(7),
   zi => variable_datai(7),
   po => tree44
);

bid21_INST: bd4st
	PORT MAP (
   a => fs_datao(0),
   en => chip_tri_state,
   tn => fsdatenb_strobe,
   pi => tree44,
   io => fs_data(0),
   zi => fs_datai(0),
   po => tree45
);

bid22_INST: bd4st
	PORT MAP (
   a => fs_datao(1),
   en => chip_tri_state,
   tn => fsdatenb_strobe,
   pi => tree45,
   io => fs_data(1),
   zi => fs_datai(1),
   po => tree46
);

bid23_INST: bd4st
	PORT MAP (
   a => fs_datao(2),
   en => chip_tri_state,
   tn => fsdatenb_strobe,
   pi => tree46,
   io => fs_data(2),
   zi => fs_datai(2),
   po => tree47
);

bid24_INST: bd4st
	PORT MAP (
   a => fs_datao(3),
   en => chip_tri_state,
   tn => fsdatenb_strobe,
   pi => tree47,
   io => fs_data(3),
   zi => fs_datai(3),
   po => tree48
);

bid25_INST: bd4st
	PORT MAP (
   a => fs_datao(4),
   en => chip_tri_state,
   tn => fsdatenb_strobe,
   pi => tree48,
   io => fs_data(4),
   zi => fs_datai(4),
   po => tree49
);

bid26_INST: bd4st
	PORT MAP (
   a => fs_datao(5),
   en => chip_tri_state,
   tn => fsdatenb_strobe,
   pi => tree49,
   io => fs_data(5),
   zi => fs_datai(5),
   po => tree50
);

bid27_INST: bd4st
	PORT MAP (
   a => fs_datao(6),
   en => chip_tri_state,
   tn => fsdatenb_strobe,
   pi => tree50,
   io => fs_data(6),
   zi => fs_datai(6),
   po => tree51
);

bid28_INST: bd4st
	PORT MAP (
   a => fs_datao(7),
   en => chip_tri_state,
   tn => fsdatenb_strobe,
   pi => tree51,
   io => fs_data(7),
   zi => fs_datai(7),
   po => end_ntree
);

out01_INST: bt4r
	PORT MAP (
   a => crc_wrb_nt,
   en => chip_tri_state,
   tn => vcc,
   z => crc_write
);

out02_INST: bt4r
	PORT MAP (
   a => crc_rdb_nt,
   en => chip_tri_state,
   tn => vcc,
   z => crc_read
);

out03_INST: bt4r
	PORT MAP (
   a => crc_add0_nt,
   en => chip_tri_state,
   tn => vcc,
   z => crc_address(0)
);

out04_INST: bt4r
	PORT MAP (
   a => crc_add1_nt,
   en => chip_tri_state,
   tn => vcc,
   z => crc_address(1)
);

out05_INST: bt4r
	PORT MAP (
   a => crc_add2_nt,
   en => chip_tri_state,
   tn => vcc,
   z => crc_address(2)
);

out06_INST: bt4r
	PORT MAP (
   a => crc_add3_nt,
   en => chip_tri_state,
   tn => vcc,
   z => crc_address(3)
);

out07_INST: bt4r
	PORT MAP (
   a => crc_add4_nt,
   en => chip_tri_state,
   tn => vcc,
   z => crc_address(4)
);

out08_INST: bt4r
	PORT MAP (
   a => fifo_out_clk_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fifo_out_clock
);

out09_INST: bt4r
	PORT MAP (
   a => reset_fifo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => reset_fifo
);

out10_INST: bt4r
	PORT MAP (
   a => micro_inter_nt,
   en => chip_tri_state,
   tn => vcc,
   z => micro_interrupt
);

out11_INST: bt4r
	PORT MAP (
   a => txco_nt,
   en => chip_tri_state,
   tn => vcc,
   z => txc
);

out12_INST: bt4r
	PORT MAP (
   a => iom_duo_nt,
   en => chip_tri_state,
   tn => open_collector_nt,
   z => iom_du
);

out13_INST: bt4r
	PORT MAP (
   a => prescale_1mo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => prescale_1m
);

out14_INST: bt4r
	PORT MAP (
   a => prescale_8mo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => prescale_8m
);

out15_INST: bt4r
	PORT MAP (
   a => variable_add0_nt,
   en => chip_tri_state,
   tn => vcc,
   z => variable_address(0)
);

out16_INST: bt4r
	PORT MAP (
   a => variable_add1_nt,
   en => chip_tri_state,
   tn => vcc,
   z => variable_address(1)
);

out17_INST: bt4r
	PORT MAP (
   a => variable_add2_nt,
   en => chip_tri_state,
   tn => vcc,
   z => variable_address(2)
);

out18_INST: bt4r
	PORT MAP (
   a => variable_add3_nt,
   en => chip_tri_state,
   tn => vcc,
   z => variable_address(3)
);

out19_INST: bt4r
	PORT MAP (
   a => variable_add4_nt,
   en => chip_tri_state,
   tn => vcc,
   z => variable_address(4)
);

out20_INST: bt4r
	PORT MAP (
   a => variable_add5_nt,
   en => chip_tri_state,
   tn => vcc,
   z => variable_address(5)
);

out21_INST: bt4r
	PORT MAP (
   a => variable_add6_nt,
   en => chip_tri_state,
   tn => vcc,
   z => variable_address(6)
);

out22_INST: bt4r
	PORT MAP (
   a => variable_add7_nt,
   en => chip_tri_state,
   tn => vcc,
   z => variable_address(7)
);

out23_INST: bt4r
	PORT MAP (
   a => variable_rdbo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => variable_rdb
);

out24_INST: bt4r
	PORT MAP (
   a => variable_wrbo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => variable_wrb
);

out25_INST: bt4r
	PORT MAP (
   a => fs_add0_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(0)
);

out26_INST: bt4r
	PORT MAP (
   a => fs_add1_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(1)
);

out27_INST: bt4r
	PORT MAP (
   a => fs_add2_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(2)
);

out28_INST: bt4r
	PORT MAP (
   a => fs_add3_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(3)
);

out29_INST: bt4r
	PORT MAP (
   a => fs_add4_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(4)
);

out30_INST: bt4r
	PORT MAP (
   a => fs_add5_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(5)
);

out31_INST: bt4r
	PORT MAP (
   a => fs_add6_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(6)
);

out32_INST: bt4r
	PORT MAP (
   a => fs_add7_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(7)
);

out33_INST: bt4r
	PORT MAP (
   a => fs_add8_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(8)
);

out34_INST: bt4r
	PORT MAP (
   a => fs_add9_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(9)
);

out35_INST: bt4r
	PORT MAP (
   a => fs_add10_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(10)
);

out36_INST: bt4r
	PORT MAP (
   a => fs_add11_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(11)
);

out37_INST: bt4r
	PORT MAP (
   a => fs_add12_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(12)
);

out38_INST: bt4r
	PORT MAP (
   a => fs_add13_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(13)
);

out39_INST: bt4r
	PORT MAP (
   a => fs_add14_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(14)
);

out40_INST: bt4r
	PORT MAP (
   a => fs_add15_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(15)
);

out41_INST: bt4r
	PORT MAP (
   a => fs_add16_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(16)
);

out42_INST: bt4r
	PORT MAP (
   a => fs_add17_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(17)
);

out43_INST: bt4r
	PORT MAP (
   a => fs_add18_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fs_address(18)
);

out44_INST: bt4r
	PORT MAP (
   a => amuxselo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => amuxsel
);

out45_INST: bt4r
	PORT MAP (
   a => fsoeo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fsoe
);

out46_INST: bt4r
	PORT MAP (
   a => fsweo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fswe
);

out47_INST: bt4r
	PORT MAP (
   a => fsstro_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fsstr
);

out48_INST: bt4r
	PORT MAP (
   a => fscso_nt,
   en => chip_tri_state,
   tn => vcc,
   z => fscs
);

out49_INST: bt4r
	PORT MAP (
   a => srdyo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => srdy
);

out50_INST: bt4r
	PORT MAP (
   a => cpfsweo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => cpfswe
);

out51_INST: bt4r
	PORT MAP (
   a => cpfsrdo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => cpfsrd
);

out52_INST: bt4r
	PORT MAP (
   a => rxdo_nt,
   en => chip_tri_state,
   tn => vcc,
   z => rxd
);

END RTL;

