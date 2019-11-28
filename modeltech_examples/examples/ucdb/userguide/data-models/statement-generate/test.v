// UCDB API User Guide Example
//
// Copyright 2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.

module top;
    bottom #0 inst0();
    bottom #1 inst1();
endmodule
module bottom;
    parameter clause = 0;
    if (clause == 0)
    begin: clause0
        initial $display("hello from %m");
    end
    else    
    begin: clause1
        initial $display ("hello from %m");
    end
endmodule
