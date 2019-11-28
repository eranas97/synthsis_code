//
// Copyright 1991-2016 Mentor Graphics Corporation
//
// All Rights Reserved.
//
// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION WHICH IS THE
// PROPERTY OF MENTOR GRAPHICS CORPORATION OR ITS LICENSORS AND IS SUBJECT TO
// LICENSE TERMS.
//
// SystemVerilog Associative Array of Classes Example - Top level module
//
module top;

    class nam_dat;
        string name;
        int data;
    endclass:nam_dat


    class men_reg;
        // associative array of nam_dat with string index 
        nam_dat reg_fields[string];
        task add_field (input nam_dat field);
            reg_fields[field.name] = field;
        endtask:add_field
    endclass:men_reg

    nam_dat field; 
    men_reg foo = new;
    string s;

    initial begin
        // Create the First field
        field = new;
        field.name = "George";
        field.data = 99;
        //Assign field to dynamic array foo
        foo.add_field(field);
        `ifdef FIELD
            field = new;
        `endif
        // Create the Second Field 
        field.name = "John";
        field.data = 199;
        //////////////////////////////////////////////////////////
        // Assign field to Second element of Dynamic array foo
        // Note if the field = new has not been done even though
        // the second element is created ,all elements have the
        // the same value "John" and "199"
        //////////////////////////////////////////////////////////
        foo.add_field(field);
        `ifdef FIELD
            field = new;
        `endif
        // Create the Third Field 
        field.name = "Gilbert";
        field.data = 299;
        //////////////////////////////////////////////////////////
        // Assign field to Third element of Dynamic array foo
        // Note if the field = new has not been done even though
        // the Third element is created , all elements have the
        // the same value "Gilbert" and "299"
        //////////////////////////////////////////////////////////
        foo.add_field(field);
        if ( foo.reg_fields.first( s ) )
            do
                $display( "%s : %p\n", s, foo.reg_fields[ s ] );
            while ( foo.reg_fields.next( s ) );
    end

endmodule
