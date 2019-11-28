//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE PROPERTY OF 
// MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.
//   

`timescale 1ns/1ns
  
module cache_set(addr, data, hit, oen, wen);
  input addr, oen, wen;
  inout data;
  output hit;
  
  wire [`addr_size-1:0] addr;
  reg [`word_size-1:0] data_r;
  reg hit_r;
  
  wire [`word_size-1:0] data = data_r;
  wire hit = hit_r;

  `define size (1 << `set_size)
  `define dly 5
  reg [`word_size-1:0] data_out;

  // ---------- Local tag and data memories -----------
  reg [`word_size-1:0] data_mem[0:(1 << `set_size)-1];
  reg [`addr_size-1:`set_size] atag_mem[0:(1 << `set_size)-1];
  reg [0:(1 << `set_size)-1] valid_mem;
  
  always @(data_out or oen)
    data_r <= #(5) oen ? `word_size'bz : data_out;

  function integer hash;
     input [`addr_size-1:0] a;
     hash = a[`set_size - 1:0];
  endfunction

  task lookup_cache;
    input [`addr_size-1:0] a;
    integer i;
    reg found;
  begin
    i = hash(a);
    found = valid_mem[i] && (a[`addr_size-1:`set_size] == atag_mem[i]);
    if (found) 
      hit_r <= #5 1'b1;
    else
      hit_r <= #5 1'b0;
  end
  endtask

  task update_cache;
    input [`addr_size-1:0] a;
    input [`word_size-1:0] d;
    integer i;
  begin
    i = hash(a);
    data_mem[i] = d;
    atag_mem[i] = a[`addr_size-1:`set_size];
    valid_mem[i] = 1'b1;
  end
  endtask
  
  integer i;
  initial begin
    for (i=0; i<`size; i=i+1)
      valid_mem[i] = 0;
  end

  always @(negedge(wen) or addr)
  begin
    lookup_cache(addr);
    data_out <= data_mem[hash(addr)];
  end
  
  always @(posedge(wen))
  begin
    update_cache(addr, data);
    lookup_cache(addr);
    data_out <= data_mem[hash(addr)];
  end
endmodule

