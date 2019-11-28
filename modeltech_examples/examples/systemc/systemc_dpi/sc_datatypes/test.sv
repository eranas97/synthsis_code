module top;

import mti_scdpi::*;

//declare sc module object
scdpi_types_top     scdpi_types_sctop_inst();

   sc_fix[3:-2] i1_fix;
   sc_fix[3:-2] i2_fix;
   sc_fix[3:-2] fix_func_out;
   
   sc_fix_fast[3:-2] i1_fix_fast;
   sc_fix_fast[3:-2] i2_fix_fast;
   sc_fix_fast[3:-2] fix_fast_func_out ;

   sc_ufix[3:-2] i1_ufix;
   sc_ufix[3:-2] i2_ufix;
   sc_ufix[3:-2] ufix_func_out;

   sc_ufix_fast[3:-2]         i1_ufix_fast;
   sc_ufix_fast[3:-2]         i2_ufix_fast;
   sc_ufix_fast[3:-2]         ufix_fast_func_out;

   sc_fixed[3:-2]             i1_fixed;
   sc_fixed[3:-2]             i2_fixed;
   sc_fixed[3:-2]             fixed_func_out;
   
   sc_ufixed[3:-2]            i1_ufixed;
   sc_ufixed[3:-2]            i2_ufixed;
   sc_ufixed[3:-2]            ufixed_func_out;
   
   sc_fixed_fast[3:-2]        i1_fixed_fast;
   sc_fixed_fast[3:-2]        i2_fixed_fast;
   sc_fixed_fast[3:-2]        fixed_fast_func_out;
   
   sc_ufixed_fast[3:-2]       i1_ufixed_fast;
   sc_ufixed_fast[3:-2]       i2_ufixed_fast;   
   sc_ufixed_fast[3:-2]       ufixed_fast_func_out;   
   
   sc_signed[7:0]             i1_signed  ;
   sc_signed[7:0]             i2_signed  ;
   sc_signed[7:0]             signed_func_out  ;
   
   sc_unsigned [7:0]          i1_unsigned;  
   sc_unsigned [7:0]          i2_unsigned;  
   sc_unsigned [7:0]          unsigned_func_out;  
   
   sc_int[7:0]                i1_int;
   sc_int[7:0]                i2_int;
   sc_int[7:0]                int_func_out;
   
   sc_uint[7:0]               i1_uint;
   sc_uint[7:0]               i2_uint;
   sc_uint[7:0]               uint_func_out;
   
   sc_bigint[39:0]            i1_bigint;
   sc_bigint[39:0]            i2_bigint;
   sc_bigint[39:0]            bigint_func_out;
   
   sc_biguint[39:0]           i1_biguint;
   sc_biguint[39:0]           i2_biguint;
   sc_biguint[39:0]           biguint_func_out;

   sc_bit                     i1_bit ;    
   sc_bit                     i2_bit ;    
   sc_bit                     bit_func_out ;    
   
   sc_bv[3:0]                 i1_bv;
   sc_bv[3:0]                 i2_bv;
   sc_bv[3:0]                 bv_func_out;
   
   sc_logic                   i1_logic ;    
   sc_logic                   i2_logic ;    
   sc_logic                   logic_func_out ;    
   
   sc_lv[3:0]                 i1_lv;
   sc_lv[3:0]                 i2_lv;
   sc_lv[3:0]                 lv_func_out;
 
//**************************** imported functions **************************************
import "DPI-SC" context function void sc_fix_func(input sc_fix[3:-2] parm1,
                                                  input sc_fix[3:-2] parm2,
                                                  inout sc_fix[3:-2] func_out );

import "DPI-SC" context function void sc_ufix_func(input sc_ufix[3:-2] parm1,
                                                   input sc_ufix[3:-2] parm2,
                                                   inout sc_ufix[3:-2] func_out );

import "DPI-SC" context function void sc_fix_fast_func(input sc_fix_fast[3:-2] parm1,
                                               input sc_fix_fast[3:-2] parm2,
                                               inout sc_fix_fast[3:-2] func_out);

import "DPI-SC" context function void sc_ufix_fast_func(input sc_ufix_fast[3:-2] parm1,
                                               input sc_ufix_fast[3:-2] parm2,
                                               inout sc_ufix_fast[3:-2] func_out);

import "DPI-SC" context function void sc_fixed_func(input sc_fixed[3:-2] parm1,
                                               input sc_fixed[3:-2] parm2,
                                               inout sc_fixed[3:-2] func_out);

import "DPI-SC" context function void sc_fixed_fast_func(input sc_fixed_fast[3:-2] parm1,
                                               input sc_fixed_fast[3:-2] parm2,
                                               inout sc_fixed_fast[3:-2] func_out);

import "DPI-SC" context function void sc_ufixed_func(input sc_ufixed[3:-2] parm1,
                                               input sc_ufixed[3:-2] parm2,
                                               inout sc_ufixed[3:-2] func_out);

import "DPI-SC" context function void sc_ufixed_fast_func(input sc_ufixed_fast[3:-2] parm1,
                                               input sc_ufixed_fast[3:-2] parm2,
                                               inout sc_ufixed_fast[3:-2] func_out);

import "DPI-SC" context function void sc_signed_func(input sc_signed[7:0]  parm1,
                                                input sc_signed[7:0]  parm2,
                                                inout sc_signed[7:0]  func_out );

import "DPI-SC" context function void sc_unsigned_func(input sc_unsigned[7:0]  parm1,
                                                input sc_unsigned[7:0]  parm2,
                                                inout sc_unsigned[7:0]  func_out );

import "DPI-SC" context function void sc_int_func(input sc_int[7:0] parm1,
                                                input sc_int[7:0] parm2,
                                                inout sc_int[7:0] func_out );

import "DPI-SC" context function void sc_uint_func(input sc_uint[7:0] parm1,
                                                input sc_uint[7:0] parm2,
                                                inout sc_uint[7:0] func_out );

import "DPI-SC" context function void sc_bigint_func(input sc_bigint[39:0] parm1,
                                                input sc_bigint[39:0] parm2,
                                                inout sc_bigint[39:0] func_out );

import "DPI-SC" context function void sc_biguint_func(input sc_biguint[39:0] parm1,
                                                input sc_biguint[39:0] parm2,
                                                inout sc_biguint[39:0] func_out );


import "DPI-SC" context function void sc_bit_func(input sc_bit parm1,
                                               input sc_bit parm2,
                                               inout sc_bit func_out);

import "DPI-SC" context function void sc_bv_func(input sc_bv[3:0] parm1,
                                               input sc_bv[3:0] parm2,
                                               inout sc_bv[3:0] func_out);

import "DPI-SC" context function void sc_logic_func(input sc_logic parm1,
                                               input sc_logic parm2,
                                               inout sc_logic func_out);

import "DPI-SC" context function void sc_lv_func(input sc_lv[3:0] parm1,
                                               input sc_lv[3:0] parm2,
                                               inout sc_lv[3:0] func_out);



//**************************** TESTING sc_fix TYPE **************************************
export "DPI-SC" task sc_fix_task;
task sc_fix_task(input sc_fix[3:-2] op1, input sc_fix[3:-2] op2,
                input int opcode, output sc_fix[5:-2] task_out,
                inout sc_fix[7:-4] task_out1,
                input sc_fix[7:-4] div_op1,
                inout sc_fix[3:-2] div_out);

     case(opcode)
          0: $display("from sc_fix_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_fix_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_fix_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_fix_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_fix_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_fix_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin div_out  = div_op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2/=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator  -----PASS" ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask

//**************************** TESTING sc_ufix TYPE **************************************
export "DPI-SC" task sc_ufix_task;
task sc_ufix_task(input sc_ufix[3:-2] op1, input sc_ufix[3:-2] op2,
                input int opcode, output sc_ufix[5:-2] task_out,
                inout sc_ufix[7:-4] task_out1,
                input sc_ufix[7:-4] div_op1,
                inout sc_ufix[3:-2] div_out);
     case(opcode)
          0: $display("from sc_ufix_task op1 & op2> %b", op1&op2) ;
          1: $display("from sc_ufix_task op1 | op2---> %b", op1|op2) ;
          2: $display("from sc_ufix_task ~(op1 | op2)---> %b", ~(op1|op2));
          3: $display("from sc_ufix_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_ufix_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_ufix_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin div_out  = div_op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2 /=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator -----PASS " ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      

endtask

//**************************** TESTING sc_fix_fast_task TYPE **************************************
export "DPI-SC" task sc_fix_fast_task;
task sc_fix_fast_task(input sc_fix_fast[3:-2] op1, input sc_fix_fast[3:-2] op2,
                input int opcode, output sc_fix_fast[5:-2] task_out,
                inout sc_fix_fast[7:-4] task_out1,
                input sc_fix_fast[7:-4] div_op1,
                inout sc_fix_fast[3:-2] div_out);

     case(opcode)
          0: $display("from sc_fix_fast_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_fix_fast_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_fix_fast_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_fix_fast_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_fix_fast_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_fix_fast_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin div_out  = div_op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2/=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator  -----PASS" ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask

//**************************** TESTING sc_ufix_fast TYPE **************************************
export "DPI-SC" task sc_ufix_fast_task;
task sc_ufix_fast_task(input sc_ufix_fast[3:-2] op1, input sc_ufix_fast[3:-2] op2,
                input int opcode, output sc_ufix_fast[5:-2] task_out,
                inout sc_ufix_fast[7:-4] task_out1,
                input sc_ufix_fast[7:-4] div_op1,
                inout sc_ufix_fast[3:-2] div_out);
     case(opcode)
          0: $display("from sc_ufix_fast_task op1 & op2> %b", op1&op2) ;
          1: $display("from sc_ufix_fast_task op1 | op2---> %b", op1|op2) ;
          2: $display("from sc_ufix_fast_task ~(op1 | op2)---> %b", ~(op1|op2));
          3: $display("from sc_ufix_fast_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_ufix_fast_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_ufix_fast_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin div_out  = div_op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2 /=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator -----PASS " ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      

endtask


//**************************** TESTING sc_fixed TYPE **************************************
export "DPI-SC" task sc_fixed_task;
task sc_fixed_task(input sc_fixed[3:-2] op1, input sc_fixed[3:-2] op2,
                input int opcode, output sc_fixed[5:-2] task_out,
                inout sc_fixed[7:-4] task_out1,
                input sc_fixed[7:-4] div_op1,
                inout sc_fixed[3:-2] div_out);
     case(opcode)
          0: $display("from sc_fixed_task op1 & op2> %b", op1&op2) ;
          1: $display("from sc_fixed_task op1 | op2---> %b", op1|op2) ;
          2: $display("from sc_fixed_task ~(op1 | op2)---> %b", ~(op1|op2));
          3: $display("from sc_fixed_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_fixed_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_fixed_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin div_out  = div_op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2 /=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator -----PASS " ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      

endtask



//**************************** TESTING sc_fixed_fast TYPE **************************************
export "DPI-SC" task sc_fixed_fast_task;
task sc_fixed_fast_task(input sc_fixed_fast[3:-2] op1, input sc_fixed_fast[3:-2] op2,
                input int opcode, output sc_fixed_fast[5:-2] task_out,
                inout sc_fixed_fast[7:-4] task_out1,
                input sc_fixed_fast[7:-4] div_op1,
                inout sc_fixed_fast[3:-2] div_out);
      real op1_div;
      op1_div = 4.25;
     case(opcode)
          0: $display("from sc_fixed_fast_task op1 & op2> %b", op1&op2) ;
          1: $display("from sc_fixed_fast_task op1 | op2---> %b", op1|op2) ;
          2: $display("from sc_fixed_fast_task ~(op1 | op2)---> %b", ~(op1|op2));
          3: $display("from sc_fixed_fast_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_fixed_fast_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_fixed_fast_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin div_out  = div_op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2 /=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator -----PASS " ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      

endtask

//**************************** TESTING sc_ufixed TYPE **************************************
export "DPI-SC" task sc_ufixed_task;
task sc_ufixed_task(input sc_ufixed[3:-2] op1, input sc_ufixed[3:-2] op2,
                input int opcode, output sc_ufixed[5:-2] task_out,
                inout sc_ufixed[7:-4] task_out1,
                input sc_ufixed[7:-4] div_op1,
                inout sc_ufixed[3:-2] div_out);
     case(opcode)
          0: $display("from sc_ufixed_task op1 & op2> %b", op1&op2) ;
          1: $display("from sc_ufixed_task op1 | op2---> %b", op1|op2) ;
          2: $display("from sc_ufixed_task ~(op1 | op2)---> %b", ~(op1|op2));
          3: $display("from sc_ufixed_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_ufixed_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_ufixed_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin div_out  = div_op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2 /=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator -----PASS " ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      

endtask

//**************************** TESTING sc_ufixed_fast TYPE **************************************
export "DPI-SC" task sc_ufixed_fast_task;
task sc_ufixed_fast_task(input sc_ufixed_fast[3:-2] op1, input sc_ufixed_fast[3:-2] op2,
                input int opcode, output sc_ufixed_fast[5:-2] task_out,
                inout sc_ufixed_fast[7:-4] task_out1,
                input sc_ufixed_fast[7:-4] div_op1,
                inout sc_ufixed_fast[3:-2] div_out);
      real op1_div;
      op1_div = 4.25;
     case(opcode)
          0: $display("from sc_ufixed_fast_task op1 & op2> %b", op1&op2) ;
          1: $display("from sc_ufixed_fast_task op1 | op2---> %b", op1|op2) ;
          2: $display("from sc_ufixed_fast_task ~(op1 | op2)---> %b", ~(op1|op2));
          3: $display("from sc_ufixed_fast_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_ufixed_fast_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_ufixed_fast_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin div_out  = div_op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2 /=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator -----PASS " ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      

endtask
//**************************** TESTING sc_signed TYPE **************************************
export "DPI-SC" task sc_signed_task;
task sc_signed_task(input sc_signed[7:0] op1, input sc_signed[7:0] op2,
                input int opcode, output sc_signed[7:0] task_out,
                inout sc_signed[7:0] task_out1);

     case(opcode)
          0: $display("from sc_signed_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_signed_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_signed_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_signed_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_signed_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_signed_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin task_out1  = op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2/=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator  -----PASS" ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask

//**************************** TESTING sc_unsigned TYPE **************************************
export "DPI-SC" task sc_unsigned_task;
task sc_unsigned_task(input sc_unsigned[7:0] op1, input sc_unsigned[7:0] op2,
                input int opcode, output sc_unsigned[7:0] task_out,
                inout sc_unsigned[7:0] task_out1);

     case(opcode)
          0: $display("from sc_unsigned_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_unsigned_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_unsigned_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_unsigned_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_unsigned_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_unsigned_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin task_out1  = op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2/=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator  -----PASS" ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask

//**************************** TESTING sc_int TYPE **************************************
export "DPI-SC" task sc_int_task;
task sc_int_task(input sc_int[7:0] op1, input sc_int[7:0] op2,
                input int opcode, output sc_int[7:0] task_out,
                inout sc_int[7:0] task_out1);

     case(opcode)
          0: $display("from sc_int_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_int_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_int_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_int_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_int_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_int_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin task_out1  = op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2/=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator  -----PASS" ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask


//**************************** TESTING sc_uint TYPE **************************************
export "DPI-SC" task sc_uint_task;
task sc_uint_task(input sc_uint[7:0] op1, input sc_uint[7:0] op2,
                input int opcode, output sc_uint[7:0] task_out,
                inout sc_uint[7:0] task_out1);

     case(opcode)
          0: $display("from sc_uint_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_uint_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_uint_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_uint_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_uint_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_uint_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin task_out1  = op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2/=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator  -----PASS" ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask


//**************************** TESTING sc_bigint TYPE **************************************
export "DPI-SC" task sc_bigint_task;
task sc_bigint_task(input sc_bigint[39:0] op1, input sc_bigint[39:0] op2,
                input int opcode, output sc_bigint[127:0] task_out,
                inout sc_bigint[127:0] task_out1);

     case(opcode)
          0: $display("from sc_bigint_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_bigint_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_bigint_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_bigint_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_bigint_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_bigint_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin task_out1  = op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2/=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator  -----PASS" ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask

//**************************** TESTING sc_biguint TYPE **************************************
export "DPI-SC" task sc_biguint_task;
task sc_biguint_task(input sc_biguint[39:0] op1, input sc_biguint[39:0] op2,
                input int opcode, output sc_biguint[127:0] task_out,
                inout sc_biguint[127:0] task_out1);

     case(opcode)
          0: $display("from sc_biguint_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_biguint_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_biguint_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_biguint_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_biguint_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_biguint_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin task_out1  = op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2/=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator  -----PASS" ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask

//**************************** TESTING sc_bit TYPE **************************************
export "DPI-SC" task sc_bit_task;
task sc_bit_task(input sc_bit op1, input sc_bit op2,
                input int opcode, output sc_bit task_out,
                inout sc_bit task_out1);

     case(opcode)
          0: $display("from sc_bit_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_bit_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_bit_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_bit_task op1 ^ op2 ---> %b", op1 ^ op2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin task_out1  = op1/op2; $display("op1 / op2 = " );end
          default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask


//**************************** TESTING sc_bv TYPE **************************************
export "DPI-SC" task sc_bv_task;
task sc_bv_task(input sc_bv[3:0] op1, input sc_bv[3:0] op2,
                input int opcode, output sc_bv[7:0] task_out,
                inout sc_bv[7:0] task_out1);

     case(opcode)
          0: $display("from sc_bv_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_bv_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_bv_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_bv_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_bv_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_bv_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin task_out1  = op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2/=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator  -----PASS" ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask
//**************************** TESTING sc_logic TYPE **************************************
export "DPI-SC" task sc_logic_task;
task sc_logic_task(input sc_logic op1, input sc_logic op2,
                input int opcode, output sc_logic task_out,
                inout sc_logic task_out1);

     case(opcode)
          0: $display("from sc_logic_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_logic_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_logic_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_logic_task op1 ^ op2 ---> %b", op1 ^ op2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin task_out1  = op1/op2; $display("op1 / op2 = " );end
          default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask


//**************************** TESTING sc_lv TYPE **************************************
export "DPI-SC" task sc_lv_task;
task sc_lv_task(input sc_lv[3:0] op1, input sc_lv[3:0] op2,
                input int opcode, output sc_lv[7:0] task_out,
                inout sc_lv[7:0] task_out1);

     case(opcode)
          0: $display("from sc_lv_task op1 & op2---> %b", op1 & op2) ;
          1: $display("from sc_lv_task op1 | op2---> %b", op1 | op2) ;
          2: $display("from sc_lv_task ~(op1 | op2)---> %b", ~(op1 | op2) ) ;
          3: $display("from sc_lv_task op1 ^ op2 ---> %b", op1 ^ op2);
          4: $display("from sc_lv_task op2 << 2 = %b", op2 << 2);
          5: $display("from sc_lv_task op2 >> 2 = %b", op2 >> 2);
          6: begin task_out  = op1+op2; $display("op1 + op2 = " );end
          7: begin task_out  = op1-op2; $display("op1 - op2 = " );end
          8: begin task_out1  = op1*op2; $display("op1 * op2 = " );end
          9: begin task_out1  = op1/op2; $display("op1 / op2 = " );end
          10:begin
               if(op2 != 0) $display("testing != operator -----PASS") ;
               if(op2 == 5) $display(" testing == operator -----PASS");
     
               op2/=op2; 
               op2 --; 
               if(op2 == 0) begin 
                    $display("testing -- operator -----PASS");
               end
     
               op2 ++;
               if(op2 != 0) begin
                    $display("testing ++ operator -----PASS"); 
               end
               
               if (op2[0] == 1)begin 
                    $display("testing bit select [] operator  -----PASS" ); 
               end
               end
            default $display ("task_out is not assigned a value !!!!!!");
      endcase      
            
endtask


initial
     begin
         i1_fix = 6'b101011;      //-5.25
         i2_fix = 6'b101111;      //-4.25

         i1_ufix = 6'b001101;      //3.25
         i2_ufix = 6'b001001;      //2.25

         i1_fix_fast = 6'b101011;  
         i2_fix_fast = 6'b101111;   

         i1_ufix_fast = 6'b101011;  
         i2_ufix_fast = 6'b101111;    

         i1_fixed = 6'b101011;    
         i2_fixed = 6'b101111;    

         i1_fixed_fast = 6'b101011;   
         i2_fixed_fast = 6'b101111;   

         i1_ufixed = 6'b101011;    
         i2_ufixed = 6'b101111;    

         i1_ufixed_fast = 6'b101011;   
         i2_ufixed_fast = 6'b101111;   

         i1_signed = -9;
         i2_signed = -8;

         i1_unsigned = 6;
         i2_unsigned = 7;

         i1_int = -3;
         i2_int = -4;

         i1_uint = 6;
         i2_uint = 5;

         i1_bigint = 40'h2ABBCCDDE;
         i2_bigint = 40'h2ABBCCDDF;

         i1_biguint = 40'h2ABBCCDDA; 
         i2_biguint = 40'h2ABBCCDDB;      

         i1_bit = 1'b0;
         i2_bit = 1'b1;


         i1_bv[3:0] = 4'b1011;      
         i2_bv[3:0] = 6'b1100;      

         i1_logic = 1'b0;      
         i2_logic = 1'b1;      

         i1_lv[3:0] = 4'b1010;      
         i2_lv[3:0] = 6'b1001;      



          sc_fix_func(i1_fix, i2_fix,fix_func_out);
          $display("from vlog fix_func_out-----> %b ",fix_func_out  );
          
          sc_fix_fast_func(i1_fix_fast,i2_fix_fast ,fix_fast_func_out );
          $display("from vlog fix_fast_func_out-----> %b ",fix_fast_func_out  );
          
          sc_ufix_func(i1_ufix, i2_ufix,ufix_func_out);
          $display("from vlog ufix_func_out-----> %b ",ufix_func_out  );
          
          sc_ufix_fast_func(i1_ufix_fast, i2_ufix_fast,ufix_fast_func_out);
          $display("from vlog ufix_fast_func_out-----> %b ",ufix_fast_func_out  );
          
          sc_fixed_func(i1_fixed, i2_fixed,fixed_func_out);
          $display("from vlog fixed_func_out-----> %b ",fixed_func_out  );
          
          sc_ufixed_func(i1_ufixed, i2_ufixed,ufixed_func_out);
          $display("from vlog ufixed_func_out-----> %b ",ufixed_func_out  );
          
          sc_fixed_fast_func(i1_fixed_fast, i2_fixed_fast,fixed_fast_func_out);
          $display("from vlog fixed_fast_func_out-----> %b ",fixed_fast_func_out  );
          
          sc_ufixed_fast_func(i1_ufixed_fast, i2_ufixed_fast,ufixed_fast_func_out);
          $display("from vlog ufixed_fast_func_out-----> %b ",ufixed_fast_func_out  );
          
          sc_signed_func(i1_signed,i2_signed,signed_func_out );
          $display("from vlog signed_func_out-----> %b ",signed_func_out  );
          
          sc_unsigned_func(i1_unsigned, i2_unsigned,unsigned_func_out);
          $display("from vlog unsigned_func_out-----> %b ",unsigned_func_out  );

          sc_int_func(i1_int, i2_int,int_func_out );
          $display("from vlog int_func_out-----> %b ",int_func_out  );
          
          sc_uint_func(i1_uint, i2_uint,uint_func_out);
          $display("from vlog uint_func_out-----> %b ",uint_func_out  );
          
          sc_bigint_func(i1_bigint, i2_bigint,bigint_func_out );
          $display("from vlog bigint_func_out-----> %b ",bigint_func_out  );
          
          sc_biguint_func(i1_biguint, i2_biguint,biguint_func_out);
          $display("from vlog biguint_func_out-----> %b ",biguint_func_out  );
          
          sc_bit_func(i1_bit, i2_bit,bit_func_out );
          $display("from vlog bit_func_out-----> %b ",bit_func_out  );
          
          sc_bv_func(i1_bv, i2_bv,bv_func_out ) ;
          $display("from vlog bv_func_out-----> %b ",bv_func_out  );

          sc_logic_func(i1_logic, i2_logic,logic_func_out );
          $display("from vlog logic_func_out-----> %b ",logic_func_out  );

          sc_lv_func(i1_lv, i2_lv,lv_func_out );
          $display("from vlog lv_func_out-----> %b ",lv_func_out  );

          
     end // initial
endmodule //top
