//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// Simple SystemVerilog Interface Example - Mailbox Interface
//
 
interface Mailbox_if;

    parameter type T = int;
    parameter int BOUND = 1;

    T Mailbox [$:BOUND];

    bit can_get, can_peek;
    always_comb
        can_get = (Mailbox.size > 0);
    always_comb
        can_peek = can_get;

    bit can_put;
    int num;
    always_comb
        num = Mailbox.size;
    always_comb
        can_put = (Mailbox.size < BOUND || BOUND == 0);
     
    task get(output T e);
        wait(Mailbox.size > 0);
        e = Mailbox.pop_back();
    endtask : get
     
    task peek(output T e);
        wait(Mailbox.size > 0);
        e = Mailbox[0];
    endtask : peek
     
    function int try_get(output T e);
        if(Mailbox.size > 0) begin
            e = Mailbox.pop_back();
            return(1);
        end
        else
            return(0);
    endfunction : try_get
     
    function int try_peek(output T e);
        if(Mailbox.size > 0) begin
            e = Mailbox.pop_back();
            return(1);
        end
        else
            return(0);
    endfunction : try_peek
  
    task put(input T e);
        wait(Mailbox.size < BOUND || BOUND==0);
        Mailbox.push_front(e);
    endtask : put
     
    function int try_put(input T e);
        if(Mailbox.size < BOUND || BOUND==0) begin
            Mailbox.push_front(e);
            return(1);
        end
        else
            return(0);
    endfunction : try_put
     
    modport initiator(
        input can_put,
        import put,
        import try_peek);

    modport slave(
        input can_get, can_peek,
        import get,
        import peek,
        import try_get,
        import try_peek);
         
endinterface : Mailbox_if
