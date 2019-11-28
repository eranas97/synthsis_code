module concat_tester;
  parameter SIM_TIME = 1;
  parameter TEST = 0;
  parameter CRCSeed = 2;
  parameter VARSeed = 5;
  parameter FSSeed = 50;
  parameter REGseed = 90;
  parameter DisableAllXs = 1;

// ******************************************************************
// ********************** Signal Declarations ***********************
// ******************************************************************
logic RESET; 
logic [15:0] ADDRESS;
logic RDB;
logic CSB;
logic WRB;
logic [7:0] DDATA;
wire [7:0] PDATA;
logic [7:0] ReadDATA;
logic FIFO_FULL_INDICATE;
logic FIFO_EMPTY_INDICATE;
logic IOM_DD;
logic TXD; // 0
logic CLOCK;
logic IOM_DCK;
logic IOM_SDS1;
logic IOM_SDS2;
logic IOM_DU;
wire IOM_DU_PULLUP;
logic PRESCALE_1M;
logic PRESCALE_8M;
logic MICRO_INTERRUPT;
logic [7:0] POSITION;
logic FIFO_OUT_CLOCK;
logic [7:0] FIFO_RAM_DATA;
logic RESET_FIFO;
logic CRC_READ;
logic CRC_WRITE;
wire [3:0]CRC;
logic [4:0]CRC_ADDRESS;
logic VARIABLE_RDB;
logic VARIABLE_WRB;
wire [7:0]VARIABLE_DATA;
logic [7:0]VARIABLE_ADDRESS;
wire [7:0]FS_DATA;
logic [14:0]FS_ADDRESS;
logic [18:0]ASIC_FS_ADDRESS;
logic FSOE;
logic FSWE;
logic FSCS;
logic AMUXSEL;
logic SRDY;
logic TXC;
logic FSSTR;
logic CPFSWE;
logic CPFSRD;
logic RXD;
logic MEMCSB;
logic FIFOCSB;
parameter FIFO = 2'b00;
parameter STORE = 2'b01;
parameter CHIP = 2'b10;
logic [19:0]PSEUDO;
int d, e, f, g;
int crcLocations, varLocations, fsLocations;
logic [7:0] IC_FIFO_DATA [0:255];
logic [3:0] CRC_STORE [0:31];
logic [7:0] VAR_STORE [0:255];
logic [7:0] FS_STORE [0:65535];
logic FS_FULL [0:65535];
wire [47:0] ALLOUTPUTS;
wire ERROR_CONDITION;
wire LOCATION_FULL;
integer regseed ;

assign ALLOUTPUTS = {CRC_WRITE, CRC_READ, CRC_ADDRESS, FIFO_OUT_CLOCK,
       RESET_FIFO, MICRO_INTERRUPT, TXC, IOM_DU, PRESCALE_1M,
       PRESCALE_8M, VARIABLE_ADDRESS, VARIABLE_RDB, VARIABLE_WRB,
       FS_ADDRESS, AMUXSEL, FSOE, FSWE, FSSTR, FSCS, SRDY,
       CPFSWE, CPFSRD, RXD };
       
always @(ALLOUTPUTS)
  begin
    if (DisableAllXs && ALLOUTPUTS === 48'bX)
      begin
        $display("Error : All Outputs Gone X");
        $stop(); 
      end 
  end       

task Write (
  input [15:0] ADD , input [7:0] DAT, input [1:0] DEVICE
  );
  begin
  DDATA <= 'bZZZZZZZZ ; CSB <= 1'b1 ; WRB <= 1'b1 ;
  ADDRESS <= 16'b0; RDB <= 1'b1 ;
  MEMCSB <= 1'b1; FIFOCSB <= 1'b1;
  #20 ADDRESS <= ADD ; DDATA <= DAT;
  #20;
  if ( DEVICE == FIFO ) FIFOCSB <=  1'b0 ;
  else if ( DEVICE == STORE ) MEMCSB <=  1'b0 ;
  else if ( DEVICE == CHIP ) CSB <=  1'b0 ;
  #20 WRB <= 1'b0 ;
  #488 WRB <= 1'b1 ;
  #122 MEMCSB <= 1'b1; FIFOCSB <= 1'b1; CSB <= 1'b1 ;
  #20 DDATA <= 8'bZZZZZZZZ; ADDRESS <= 16'b0;
  end
endtask

task FillCRCStore (
  input Seed
  );
  integer seed ; seed = Seed ;
  for (crcLocations=0;crcLocations<=31;crcLocations=crcLocations+1)
    begin
      CRC_STORE[crcLocations] <= $random(seed);
    end   
endtask

task FillVARStore (
  input Seed
  );
  integer seed ; seed = Seed ;
  for (varLocations=0;varLocations<=255;varLocations=varLocations+1)
    begin
      VAR_STORE[varLocations] <= $random(seed);
    end   
endtask

task FillFSStore (
  input Seed, input Zeros
  );
  integer seed ; seed = Seed ;
  for (fsLocations=0;fsLocations<=65535;fsLocations=fsLocations+1)
    begin
      if (Zeros == 0)
        begin
          FS_STORE[fsLocations] <= 8'b00000000;
        end
      else
        begin
          FS_STORE[fsLocations] <= $random(seed);
        end
    end   
endtask

task FillInformationStore (
  input [5:0] GroupID, input [5:0] ChannelID
  );
  logic [7:0] fill; logic [7:0] Wdata;
  for (fill=0;fill<=255;fill=fill+1)
    begin
        // Sync Byte
       if (fill[6:0] === 7'b0000000 || fill[6:0] === 7'b0000001 )
         begin
           Wdata = 8'b11111110 ; 
         end
       else
         // Channel ID Byte
         begin      
           if (fill[6:0] === 7'b0100000 || fill[6:0] === 7'b0100001 )
             begin
               Wdata = {1'b1, (ChannelID + fill[0]) , 1'b1 };
             end
           else
             // Group ID Byte
             begin     
               if (fill[6:0] === 7'b1000000 || fill[6:0] === 7'b1000001 )
                 begin
                   Wdata = {1'b1, GroupID , 1'b1 }  ;
                 end  
               else
                 // Random because INFO Channel should have 16 bytes
                 begin        
                   if (fill[6:0] === 7'b1100000 || fill[6:0] === 7'b1100001 )
                     begin
                       Wdata = 8'b11010101  ;
                     end
                   else
                     begin
                       Wdata = 8'b00000000;
                     end
                 end
             end
         end  
       Write (16'h0000, Wdata, FIFO);
    end 
endtask

task Read (
  input [15:0] ADD, input [1:0] DEVICE
  );
  begin
  CSB <= 1'b1 ; WRB <= 1'b1 ;
  ADDRESS <= 16'b0; RDB <= 1'b1 ;
  MEMCSB <= 1'b1; FIFOCSB <= 1'b1;
  #20 ADDRESS <= ADD ;
  #20;
  if ( DEVICE == FIFO ) FIFOCSB <=  1'b0 ;
  else if ( DEVICE == STORE ) MEMCSB <=  1'b0 ;
  else if ( DEVICE == CHIP ) CSB <=  1'b0 ;
  #20 RDB <= 1'b0 ;
  #488 RDB <= 1'b1 ;
  $display("%t Read Register %d Got Data %b\n",$time,ADDRESS,PDATA);
  ReadDATA <= PDATA;
  #122 MEMCSB <= 1'b1; FIFOCSB <= 1'b1; CSB <= 1'b1 ;
  #20 ADDRESS <= 16'b0;
  end
endtask

// ******************************************************************
// ******************* Behavioural Code used for system *************
// ******************************************************************
// Generates the two system clocks
// phase locked to each other.

initial // Clock generator
  begin
    CLOCK = 0;
    forever #61 CLOCK = !CLOCK;
  end
  
initial // Reset generator
  begin
    RESET = 1'b0;
    #20000 RESET = 1'b1;
  end
  
initial // Simulation Run time Control
  begin
    #(SIM_TIME * 1000000);
    $display("Simulation Finished"); 
    $stop();
  end
  
initial // DCK Clock generator
  begin
    IOM_DCK <= 1'b0;  
    #1;
    forever
    begin
      for (e=1;e<=4;e=e+1)
      begin
        #244 IOM_DCK <= 1'b0;
        #366 IOM_DCK <= 1'b1;
      end 
      for (d=1;d<=2;d=d+1)
      begin
        #366 IOM_DCK <= 1'b0;
        #366 IOM_DCK <= 1'b1;
      end  
    end
  end  

// **** Generates the strobes from the ISDN module *********************************
initial // IOM Strobe generator
  begin
    IOM_SDS1 <= 1'b0; IOM_SDS2 <= 1'b0;  
    #1;
    forever
    begin
      #2      IOM_SDS1 <= 1'b1;
              IOM_SDS2 <= 1'b0;
      #10248  IOM_SDS1 <= 1'b0;
              IOM_SDS2 <= 1'b1;
      #10492  IOM_SDS2 <= 1'b0;
      #104186;
    end
  end 

// **** Transmit process variable RAM  ********************************************
always @(posedge CRC_WRITE)
  begin
    CRC_STORE[CRC_ADDRESS] <= CRC;
  end
assign CRC = (CRC_READ == 1'b0) ? CRC_STORE[CRC_ADDRESS] : 4'bZZZZ ;  

// **** Receive process variable RAM  ********************************************
always @(posedge VARIABLE_WRB)
  begin
    VAR_STORE[VARIABLE_ADDRESS] <= VARIABLE_DATA;
  end
assign VARIABLE_DATA = (VARIABLE_RDB == 1'b0) ? VAR_STORE[VARIABLE_ADDRESS] : 8'bZZZZZZZZ ;

// Var0 ------ ------ ------ ------ CRCVL3 CRCVL2 CRCVL1 CRCVL0
// Var1 ------ ------ GRPID5 GRPID4 GRPID3 GRPID2 GRPID1 GRPID0
// Var2 CRCST1 CRCST0 ------ CHNID4 CHNID3 CHNID2 CHNID1 CHNID0
// Var3 GRPST1 GRPST0 ------ ------ ------ ------ CHNST1 CHNST0
// Var4 ------ ------ FRMST1 FRMST0 ------ ------ ICNST1 ICNST0
// Var5 OCTCT7 OCTCT6 OCTCT5 OCTCT4 OCTCT3 OCTCT2 OCTCT1 OCTCT0
// Var6 ------ FAWST2 FAWST1 FAWST0 ICCNT3 ICCNT2 ICCNT1 ICCNT0
// Var7 ------ ------ STFRM5 STFRM4 STFRM3 STFRM2 STFRM1 STFRM0

typedef enum {
   OUT_OF_SYNC, SEEN_ONCE, SEEN_TWICE, IN_SYNC, MISSED_ONCE, MISSED_TWICE
} faw_t;

typedef enum {
   Enabled, SeenOnce, SeenTwice, Disabled
} crc_t;

typedef enum {
   Search, Match, Found, Error
} state_t;

typedef enum {
   SEARCH, MATCH, FOUND_TWICE, FROZEN
} persist_state_t;

covergroup monitor_channel_data (ref faw_t FawState, ref crc_t CRCState, ref persist_state_t GroupState,
                                 ref persist_state_t ChannelState, ref state_t FrameState,
                                 ref state_t InfoState ) @(posedge VARIABLE_WRB); 
  FAW : coverpoint  FawState iff (RESET)
  { 
    bins OUT_OF_SYNC  = { 0 }; bins SEEN_ONCE    = { 1 };
    bins SEEN_TWICE   = { 2 }; bins IN_SYNC      = { 3 };
    bins MISSED_ONCE  = { 4 }; bins MISSED_TWICE = { 5 };
    bins others = default;
  }
  CRC : coverpoint CRCState iff (RESET)
  { 
    bins ENABLED       = { 0 }; bins SEEN_ONCE     = { 1 };
    bins SEEN_TWICE    = { 2 }; bins DISABLED      = { 3 };
    bins others = default;
  }
  GROUP : coverpoint GroupState iff (RESET)
  { 
    bins SEARCH      = { 0 }; bins MATCH       = { 1 };
    bins FOUND_TWICE = { 2 }; bins FROZEN      = { 3 };
    bins others = default;
  }   
  CHANNEL : coverpoint ChannelState iff (RESET)
  { 
    bins SEARCH      = { 0 }; bins MATCH       = { 1 };
    bins FOUND_TWICE = { 2 }; bins FROZEN      = { 3 };
    bins others = default;
  }   
  FRAME : coverpoint FrameState iff (RESET)
  { 
    bins SEARCH      = { 0 }; bins MATCH       = { 1 };
    bins FOUND = { 2 };       bins ERROR      = { 3 };
    bins others = default;
  }   
  INFO : coverpoint InfoState iff (RESET)
  { 
    bins SEARCH      = { 0 }; bins MATCH       = { 1 };
    bins FOUND = { 2 };       bins ERROR      = { 3 };
    bins others = default;
  }
  option.per_instance = 1;
endgroup

faw_t FawState0, FawState1;
persist_state_t GroupState0, GroupState1;
persist_state_t ChannelState0,ChannelState1;
crc_t CRCState0, CRCState1;
state_t FrameState0,FrameState1;
state_t InfoState0,InfoState1;

assign FawState0 = VAR_STORE[6][6:4];
assign CRCState0 = VAR_STORE[2][7:6];
assign GroupState0 = VAR_STORE[3][7:6];
assign ChannelState0 = VAR_STORE[3][1:0];
assign FrameState0 = VAR_STORE[4][5:4];
assign InfoState0 = VAR_STORE[4][1:0];
monitor_channel_data monitor_channel_data_chan0 = 
   new(FawState0, CRCState0, GroupState0, ChannelState0, FrameState0, InfoState0);
   
assign FawState1 = VAR_STORE[14][6:4];
assign CRCState1 = VAR_STORE[10][7:6];
assign GroupState1 = VAR_STORE[11][7:6];
assign ChannelState1 = VAR_STORE[11][1:0];
assign FrameState1 = VAR_STORE[12][5:4];
assign InfoState1 = VAR_STORE[12][1:0];
monitor_channel_data monitor_channel_data_chan1 = 
   new(FawState1, CRCState1, GroupState1, ChannelState1, FrameState1, InfoState1);

// **** Frame Store RAM  ********************************************************
always @(posedge FSWE)
  begin
    if (FSCS == 1'b0)
      begin
        if (MEMCSB == 1'b0)
          FS_STORE[FS_ADDRESS] <= PDATA;
        else 
          FS_STORE[FS_ADDRESS] <= FS_DATA;
          FS_FULL[FS_ADDRESS] <= 1'b1;
      end
  end
always @(posedge FSOE)
  begin
    if (FSCS == 1'b0)
      begin
        FS_FULL[FS_ADDRESS] <= 1'b0;
      end
  end
  
assign LOCATION_FULL = FS_FULL[FS_ADDRESS];

property location_full_on_write (FSCS, LOCATION_FULL);
  @(posedge FSWE) disable iff (FSCS) LOCATION_FULL == 1'b1;
endproperty
assert property (location_full_on_write(FSCS,LOCATION_FULL));

property location_empty_on_read (FSCS, LOCATION_FULL);
  @(posedge FSOE) disable iff (FSCS) LOCATION_FULL == 1'b0;
endproperty
assert property (location_empty_on_read(FSCS,LOCATION_FULL));
  
assign FS_DATA = (FSOE == 1'b0 && FSCS == 1'b0 ) ? FS_STORE[FS_ADDRESS] : 8'bZZZZZZZZ ;

assign #2 FS_ADDRESS = (AMUXSEL == 1'b0) ? ADDRESS[14:0] : {ASIC_FS_ADDRESS[18:5], ASIC_FS_ADDRESS[0]} ;

// **** Fifo Model *****************************************************************
initial POSITION = 0;
always @(posedge FIFO_OUT_CLOCK)
  begin
    if (POSITION != 0)
      begin
        POSITION <= POSITION - 1;
      end
  end
always @(posedge WRB)
  begin
    if (FIFOCSB == 1'b0)
      begin
        if (POSITION != 255)
          begin
            POSITION <= POSITION + 1;
            IC_FIFO_DATA[POSITION] <= PDATA;
          end
      end
  end
always @(POSITION)
  begin
    if (POSITION == 255)
      begin
        FIFO_FULL_INDICATE <= 1'b0;
        FIFO_EMPTY_INDICATE <= 1'b1;  
      end
    else if (POSITION == 0)
      begin
        FIFO_FULL_INDICATE <= 1'b1;
        FIFO_EMPTY_INDICATE <= 1'b0;          
      end
    else
      begin
        FIFO_FULL_INDICATE <= 1'b1;
        FIFO_EMPTY_INDICATE <= 1'b1;           
      end
  end
assign FIFO_RAM_DATA = IC_FIFO_DATA[POSITION];
covergroup monitor_fifo_reads @(posedge FIFO_OUT_CLOCK); 
  coverpoint POSITION iff (RESET)
  { 
    bins LowMark = { 0 };
    bins HalfCap = { [1:127] }; 
    bins FullCap = { [128:254] }; 
    bins HighMark = { 255 };   
    bins others = default;
  }
endgroup
monitor_fifo_reads monitor_fifo_reads_c1 = new;
covergroup monitor_fifo_writes @(posedge WRB); 
  coverpoint POSITION iff (!FIFOCSB)
  { 
    bins LowMark = { 0 };
    bins HalfCap = { [1:127] }; 
    bins FullCap = { [128:254] }; 
    bins HighMark = { 255 };   
    bins others = default;
  }
endgroup
monitor_fifo_writes monitor_fifo_writes_c1 = new; 

// **** Simulates the host interface with read/writes ******************************
initial // Host generator
  begin
    DDATA <= 8'bZZZZZZZZ ; CSB <= 1'b1 ; WRB <= 1'b1 ;
    ADDRESS <= 16'b0; RDB <= 1'b1 ;
    MEMCSB <= 1'b1; FIFOCSB <= 1'b1;
    FillCRCStore (CRCSeed);
    FillVARStore (VARSeed);
    FillFSStore  (FSSeed,1);
    #20000;
    if (TEST == 1 || TEST == 6)
      begin
        FillFSStore  (FSSeed,0);
        FillInformationStore ( 6'b000011, 6'b000000);
        Write (16'b0000, 8'b00101001, CHIP); // ACK,FIFORST,MOD1,MOD0,STAT1,STAT0,ADDC,CRCENB
        Read  (16'b0000, CHIP);
        Write (16'b0010, 8'b00000010, CHIP); // CHAN4,CHAN3,CHAN2,CHAN1,CHAN0 -- Number Of Enabled Channels
        Read  (16'b0010, CHIP); 
        Write (16'b0100, 8'b00000011, CHIP); // GID4,GID3,GID2,GID1,GID0 -- GroupID for the call
        Read  (16'b0100, CHIP);         
        Write (16'b0101, 8'b00000010, CHIP); // TXP,SWAPB,SWPC,SERCH,TSTMD,CLAM,DMOD,VRST - SERCH <- Disables the post processor
        Read  (16'b0101, CHIP);
      end
    if (TEST == 2)
      begin
        Write (16'h0000, 8'b00001111, CHIP); // ACK,FIFORST,MOD1,MOD0,STAT1,STAT0,ADDC,CRCENB
        Read  (16'h0000, CHIP);
        Write (16'h0002, 8'b00010101, CHIP); // CHAN4,CHAN3,CHAN2,CHAN1,CHAN0 -- Number Of Enabled Channels
        Read  (16'h0002, CHIP);
        Write (16'h0004, 8'b00010101, CHIP); // GID4,GID3,GID2,GID1,GID0 -- GroupID for the call
        Read  (16'h0004, CHIP);       
        Write (16'h0005, 8'b01000111, CHIP); // TXP,SWAPB,SWPC,SERCH,TSTMD,CLAM,DMOD,VRST - SERCH <- Disables the post processor
        Read  (16'h0005, CHIP);
      end
    if (TEST == 3)
      begin
        for (f=0;f<=511;f=f+1)
          begin
            Write (16'h0000, f, FIFO);
          end 
      end
    if (TEST == 4) 
      begin
        for (g=0;g<=65535;g=g+1)
          begin
            Write (g, g, STORE);
            Read  (g, STORE);
          end          
      end
    if (TEST == 7)
      begin
        Write (16'b0000, 8'b00111111, CHIP); // ACK,FIFORST,MOD1,MOD0,STAT1,STAT0,ADDC,CRCENB
        Read  (16'b0000, CHIP);
        Write (16'b0010, 8'b00000010, CHIP); // CHAN4,CHAN3,CHAN2,CHAN1,CHAN0 -- Number Of Enabled Channels
        Read  (16'b0010, CHIP); 
        Write (16'b0100, 8'b00000011, CHIP); // GID4,GID3,GID2,GID1,GID0 -- GroupID for the call
        Read  (16'b0100, CHIP);         
        Write (16'b0101, 8'b00001010, CHIP); // TXP,SWAPB,SWPC,SERCH,TSTMD,CLAM,DMOD,VRST - SERCH <- Disables the post processor
        Read  (16'b0101, CHIP);
      end
    if (TEST > 7) 
      begin
        regseed = REGseed ;  
        Write (16'h0000, $random(regseed), CHIP);
        Write (16'h0001, $random(regseed), CHIP);
        Write (16'h0002, $random(regseed), CHIP);
        Write (16'h0003, $random(regseed), CHIP);
        Write (16'h0004, $random(regseed), CHIP);
        Write (16'h0005, $random(regseed), CHIP);  
      end
    #20000;
      for (g=0;g<=65535;g=g+1)
        begin
          #500000;
          Read  (16'b0110, CHIP);
          if (ReadDATA[2] === 1'b1)
            begin
              $display("Post Processor In Sync.\n");
              g = 65535;
              $display("Unclamp RXD By Setting bit2 & Set Stat1&0 for Data Mode \n");
              Write (16'b0101, 8'b00001110, CHIP);
              Write (16'b0000, 8'b00101101, CHIP);
            end           
        end  
  end

// **** Serial Transmit Data Input *************************************************
initial PSEUDO = 20'b10010010101110111010;
always @(negedge TXC)
  begin
    PSEUDO <= {PSEUDO[18:0], ~(PSEUDO[2] ^ PSEUDO[19])};  
  end

assign TXD = (TEST == 6 || TEST == 5) ? PSEUDO[19] : 1'b1 ;

assign IOM_DU_PULLUP = (IOM_DU === 1'b0) ? 1'b0 : 1'b1;

assign IOM_DD = (TEST == 6) ? IOM_DU_PULLUP : 1'b1 ;

assign PDATA = (FSOE == 1'b0 && FSCS == 1'b0 && MEMCSB == 1'b0) ? FS_STORE[FS_ADDRESS] : DDATA ;


// ************** Covergroups *************
wire Bit7, Bit6, Bit5, Bit4, Bit3, Bit2, Bit1, Bit0;
assign Bit0 = PDATA[0];
assign Bit1 = PDATA[1];
assign Bit2 = PDATA[2];
assign Bit3 = PDATA[3];
assign Bit4 = PDATA[4];
assign Bit5 = PDATA[5];
assign Bit6 = PDATA[6];
assign Bit7 = PDATA[7];
covergroup monitor_registers @(posedge WRB); 
  coverpoint ADDRESS iff (!CSB)
  { 
    bins Register0 = { 0 };
    bins Register1 = { 1 }; 
    bins Register2 = { 2 }; 
    bins Register3 = { 3 }; 
    bins Register4 = { 4 }; 
    bins Register5 = { 5 };  
    bins others = default;
  }
  coverpoint Bit0  iff (!CSB);
  coverpoint Bit1  iff (!CSB);
  coverpoint Bit2  iff (!CSB);
  coverpoint Bit3  iff (!CSB);
  coverpoint Bit4  iff (!CSB);
  coverpoint Bit5  iff (!CSB);
  coverpoint Bit6  iff (!CSB);
  coverpoint Bit7  iff (!CSB);
  RegXbit0: cross ADDRESS, Bit0 iff (!CSB);
  RegXbit1: cross ADDRESS, Bit1 iff (!CSB);
  RegXbit2: cross ADDRESS, Bit2 iff (!CSB);
  RegXbit3: cross ADDRESS, Bit3 iff (!CSB);
  RegXbit4: cross ADDRESS, Bit4 iff (!CSB);
  RegXbit5: cross ADDRESS, Bit5 iff (!CSB);
  RegXbit6: cross ADDRESS, Bit6 iff (!CSB);
  RegXbit7: cross ADDRESS, Bit7 iff (!CSB);
endgroup 
monitor_registers monitor_registers_c1 = new;
covergroup read_registers @(posedge RDB); 
  coverpoint ADDRESS iff (!CSB)
  { 
    bins Register0  = { 0 };
    bins Register1  = { 1 }; 
    bins Register2  = { 2 }; 
    bins Register3  = { 3 }; 
    bins Register4  = { 4 }; 
    bins Register5  = { 5 };
    bins Register6  = { 6 };
    bins Register7  = { 7 }; 
    bins Register8  = { 8 }; 
    bins Register9  = { 9 }; 
    bins ErrorRegisters = default;
  }
endgroup 
read_registers read_registers_c1 = new;  
// ******************************************************************
// *********************** Component Instantiations *****************
// ******************************************************************

concat CHIPBOND (
             .RESET(RESET),
             .CLOCK(CLOCK),
             .ADDRESS(ADDRESS[3:0]),
             .PDATA(PDATA),
             .RDB(RDB),
             .CSB(CSB),
             .WRB(WRB),
             .CRC_WRITE(CRC_WRITE),
             .CRC_READ(CRC_READ),
             .CRC_ADDRESS(CRC_ADDRESS),
             .CRC(CRC),
             .FIFO_RAM_DATA(FIFO_RAM_DATA),
             .FIFO_OUT_CLOCK(FIFO_OUT_CLOCK),
             .FIFO_FULL_INDICATE(FIFO_FULL_INDICATE),
             .FIFO_EMPTY_INDICATE(FIFO_EMPTY_INDICATE),
             .RESET_FIFO(RESET_FIFO),
             .MICRO_INTERRUPT(MICRO_INTERRUPT),
             .TXC(TXC),
             .IOM_SDS1(IOM_SDS1),
             .IOM_SDS2(IOM_SDS2),
             .IOM_DCK(IOM_DCK),
             .IOM_DU(IOM_DU),
             .IOM_DD(IOM_DD),
             .PRESCALE_1M(PRESCALE_1M),
             .PRESCALE_8M(PRESCALE_8M),
             .VARIABLE_ADDRESS(VARIABLE_ADDRESS),
             .VARIABLE_RDB(VARIABLE_RDB),
             .VARIABLE_WRB(VARIABLE_WRB),
             .VARIABLE_DATA(VARIABLE_DATA),
             .FS_DATA(FS_DATA),
             .FS_ADDRESS(ASIC_FS_ADDRESS),
             .MEMCS(MEMCSB),
             .AMUXSEL(AMUXSEL),
             .FSOE(FSOE),
             .FSWE(FSWE),
             .FSSTR(FSSTR),
             .FSCS(FSCS),
             .SRDY(SRDY),
             .CPFSWE(CPFSWE),
             .CPFSRD(CPFSRD),
             .RXD(RXD),
             .TXD(TXD));

endmodule