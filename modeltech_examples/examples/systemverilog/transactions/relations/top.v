module top;
    integer stream1;
    integer stream2;
    integer stream3;
    integer stream4;
    integer stream5;
    integer t1, t2, t3, t4, t5;

    initial begin
        stream1 = $create_transaction_stream("Stream1");
        stream2 = $create_transaction_stream("Stream2");
        stream3 = $create_transaction_stream("Stream3");
        stream4 = $create_transaction_stream("Stream4");
        stream5 = $create_transaction_stream("Stream5");
    end

    always begin

        // Main transaction:
        t1 = $begin_transaction(stream1, "TR");

        // Secondary transactions:
        #1;
        if (t2 != 0) begin
            $end_transaction(t2);
            $free_transaction(t2);
        end
        t2 = $begin_transaction(stream2, "TR");
        $add_relation(t2, t1, "source");

        if (t4 != 0) begin
            $end_transaction(t4);
            $free_transaction(t4);
        end
        t4 = $begin_transaction(stream4, "TR");
        $add_relation(t4, t1, "source");

        // Tertiary  transactions:
        #1;
        if (t3 != 0) begin
            $end_transaction(t3);
            $free_transaction(t3);
        end
        t3 = $begin_transaction(stream3, "TR");
        $add_relation(t3, t2, "source");

        if (t5 != 0) begin
            $end_transaction(t5);
            $free_transaction(t5);
        end
        t5 = $begin_transaction(stream5, "TR");
        $add_relation(t5, t4, "source");

        #1;
        #1;
        $end_transaction(t1);
        $free_transaction(t1);
    end
    
endmodule
