module top;
    int stream, tr;

    initial begin
        stream = $create_transaction_stream("Stream");
        #10;
        tr = $begin_transaction(stream, "Tran1");
        $add_attribute(tr, 10, "beg");
        $add_attribute(tr, 12, "special");
        $add_attribute(tr, 14, "end");
        #4;
        $end_transaction(tr);
        $free_transaction(tr);
    end

endmodule
