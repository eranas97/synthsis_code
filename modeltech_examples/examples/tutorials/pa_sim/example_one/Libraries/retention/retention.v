`timescale 1ns/1ps

`celldefine
module DFF_RET (input CP, D, SI, SE, CDN, SDN, SAVE, NRESTORE, output Q);
    reg b_notifier, notifier;
    buf (CDN_i, CDN);
    buf (SDN_i, SDN);
    buf (CP_i, CP);
    buf (SAVE_i, SAVE);
    buf (NRESTORE_i, NRESTORE);
    mux_ret_udp (D_MUX, D, SI, SE);
    dff_ret_udp (DFF_OUT, D_MUX, CP, CDN_TOTAL, SDN_TOTAL, notifier);
    mux_ret_udp (DFF_OUT_MUX, DFF_OUT, 1'bx, 1'b0);
    dla_ret_udp (SAVED_DATA_TMP, DFF_OUT_MUX, SAVE_i, 1'b1, 1'b1, b_notifier);
    mux_ret_udp (SAVED_DATA, SAVED_DATA_TMP, 1'bx, 1'b0);
    not (NOT_SAVED_DATA, SAVED_DATA);
    or (NRESTORE0, NRESTORE, SAVED_DATA);
    or (NRESTORE1, NRESTORE, NOT_SAVED_DATA); 
    and (DFF_CDN, CDN_i, NRESTORE0);
    and (DFF_SDN, SDN_i, NRESTORE1);
    or (DFF_CDN_CP, DFF_CDN, CP);
    or (DFF_SDN_CP, DFF_SDN, CP);
    mux_ret_udp (CDN_VSS, DFF_CDN_CP, 1'bx, 1'b0);
    mux_ret_udp (SDN_VSS, DFF_SDN_CP, 1'bx, 1'b0);
    and (CDN_TOTAL, CDN_VSS, CDN);
    and (SDN_TOTAL, SDN_VSS, SDN);  
    mux_ret_udp (Q_buf, DFF_OUT_MUX, 1'bx, 1'b0);
    buf (Q, Q_buf);
    not (SE_int_not, SE);
    and (D_check, CDN_i, SDN_i, SE_int_not);
    not (nSAVE, SAVE);
    /////////////////////////////////////////////////////////////////
    // Error checks for illegal save/restore states
    ////////////////////////////////////////////////////////////////
/*    always @(SAVE_i, NRESTORE_i)
        if ((SAVE_i===1'b1)&&(NRESTORE_i===1'b0)) begin
            $display("Error: INVALID OPERATION - Both SAVE & NRESTORE are active %0t", $time);
 	    $stop;
        end
    always @(CP_i)
        if ((SAVE_i===1'b1)||(NRESTORE_i ===1'b0)) begin
            $display("Error: INVALID OPERATION - CP is toggling while SAVE or NRESTORE are active %0t", $time);
 	    $stop;
        end */
    specify
        (posedge CP => (Q+:D)) = (0, 0);
        $setuphold (posedge CP &&& D_check, posedge D, 0, 0, notifier);
        $setuphold (posedge CP &&& D_check, negedge D, 0, 0, notifier);
        $setuphold (negedge CP &&& nSAVE, posedge NRESTORE , 0, 0, notifier);
        $setuphold (posedge CP &&& NRESTORE, negedge SAVE , 0, 0, b_notifier);
    endspecify
endmodule
`endcelldefine

primitive mux_ret_udp (output q, input d0, d1, s);
    table
    // d0  d1  s   : q
    // -----------------
       0   ?   0   : 0 ;
       1   ?   0   : 1 ;
       ?   0   1   : 0 ;
       ?   1   1   : 1 ;
       0   0   x   : 0 ;
       1   1   x   : 1 ;
    endtable
endprimitive

primitive dff_ret_udp (output reg q, input d, cp, cdn, sdn, notifier);
    table
    // d  cp  cdn sdn notifier : q : q+
    // ----------------------------------------------------------------------
       ?   ?   0   ?     ?     : ? :  0 ; // CDN dominate SDN
       ?   ?   1   0     ?     : ? :  1 ; // SDN is set   
       ?   ?   1   x     ?     : 0 :  x ; // SDN affect Q
       ?   ?   1   x     ?     : 1 :  1 ; // Q=1,preset=X
       ?   ?   x   1     ?     : 0 :  0 ; // Q=0,clear=X
       0 (01)  ?   1     ?     : ? :  0 ; // Latch 0
       0   *   ?   1     ?     : 0 :  0 ; // Keep 0 (D==Q)
       1 (01)  1   ?     ?     : ? :  1 ; // Latch 1   
       1   *   1   ?     ?     : 1 :  1 ; // Keep 1 (D==Q)
       ? (1?)  1   1     ?     : ? :  - ; // ignore negative edge of clk
       ? (?0)  1   1     ?     : ? :  - ; // ignore negative edge of clk
       ?   ? (?1)  1     ?     : ? :  - ; // ignore positive edge of CDN
       ?   ?   1 (?1)    ?     : ? :  - ; // ignore posative edge of SDN
       *   ?   1   1     ?     : ? :  - ; // ignore data change on steady clk
       ?   ?   ?   ?     *     : ? :  x ; // timing check violation
    endtable
endprimitive

primitive dla_ret_udp (output reg q, input d, e, cdn, sdn, notifier);
    table
    // d  cp  cdn sdn notifier : q  : q+
    // ----------------------------------------------------------------------
       1  1    1   ?     ?     : ?  :  1  ; // Latch 1
       0  1    ?   1     ?     : ?  :  0  ; // Latch 0
       0 (10)  1   1     ?     : ?  :  0  ; // Latch 0 after falling edge
       1 (10)  1   1     ?     : ?  :  1  ; // Latch 1 after falling edge
       *  0    ?   ?     ?     : ?  :  -  ; // no changes
       ?  ?    ?   0     ?     : ?  :  1  ; // preset to 1
       ?  0    1   *     ?     : 1  :  1  ;
       1  ?    1   *     ?     : 1  :  1  ;
       1  *    1   ?     ?     : 1  :  1  ;
       ?  ?    0   1     ?     : ?  :  0  ; // reset to 0
       ?  0    *   1     ?     : 0  :  0  ;
       0  ?    *   1     ?     : 0  :  0  ;
       0  *    ?   1     ?     : 0  :  0  ;
       ?  ?    ?   ?     *     : ?  :  x  ; // toggle notifier
    endtable
endprimitive
