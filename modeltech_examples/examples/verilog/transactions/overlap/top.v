module top;
    integer stream, trh1a, trh1b, trh1c, trh1d, trh2a, trh2b, trh2c, trh2d;

    initial begin
        stream = $create_transaction_stream("Stream");


        /* overlapping phase transactions, different names */
        #4;
        trh1a = $begin_transaction(stream, "Tran_1a");
        $add_attribute(trh1a, 4, "beg");
        #2;
        trh1b = $begin_transaction(stream, "Tran_1b",,trh1a);
        $add_attribute(trh1b, 6, "beg");
        #2;
        trh1c = $begin_transaction(stream, "Tran_1c",,trh1b);
        $add_attribute(trh1c, 8, "beg");
        trh1d = $begin_transaction(stream, "Tran_1d",,trh1c);
        $add_attribute(trh1d, 8, "beg");
        trh2a = $begin_transaction(stream, "Tran_2a");
        $add_attribute(trh2a, 8, "beg");
        #2;
        $end_transaction(trh1d);
        $add_attribute(trh1d, 10, "end");
        $free_transaction(trh1d);
        trh2b = $begin_transaction(stream, "Tran_2b",,trh2a);
        $add_attribute(trh2b, 10, "beg");
        #2;
        $end_transaction(trh1c);
        $add_attribute(trh1c, 12, "end");
        $free_transaction(trh1c);
        trh2c = $begin_transaction(stream, "Tran_2c",,trh2b);
        $add_attribute(trh2c, 12, "beg");
        trh2d = $begin_transaction(stream, "Tran_2d",,trh2c);
        $add_attribute(trh2d, 12, "beg");
        #2;
        $end_transaction(trh1b);
        $add_attribute(trh1b, 14, "end");
        $free_transaction(trh1b);
        $end_transaction(trh1a);
        $add_attribute(trh1a, 14, "end");
        $free_transaction(trh1a);
        $end_transaction(trh2d);
        $add_attribute(trh2d, 14, "end");
        $free_transaction(trh2d);
        #2;
        $end_transaction(trh2c);
        $add_attribute(trh2c, 16, "end");
        $free_transaction(trh2c);
        #2;
        $end_transaction(trh2b);
        $add_attribute(trh2b, 18, "end");
        $free_transaction(trh2b);
        $end_transaction(trh2a);
        $add_attribute(trh2a, 18, "end");
        $free_transaction(trh2a);
    end

endmodule
