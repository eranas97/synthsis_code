module top;
    int stream1, stream2, trh1, trh2;
    time startTime, endTime;

    initial begin
        stream1 = $create_transaction_stream("Stream1");
        stream2 = $create_transaction_stream("Stream2");
        /* two serial, non-overlapping (serial) transactions */
        #10;                                 /* Idle period                   */
        trh1 =                               /* Start a transaction           */
               $begin_transaction(stream1, "Tran");
        $add_attribute(trh1, 10, "beg");
        #2;
        $end_transaction(trh1);              /* End the transaction           */
        $add_attribute(trh1, 12, "end");
        $free_transaction(trh1);
        #2;                                  /* Idle period                   */
        trh1 =                               /* Start another transaction     */
               $begin_transaction(stream1, "Tran");
        $add_attribute(trh1, 14, "beg");
        #2
        $end_transaction(trh1);              /* End the transaction           */
        $add_attribute(trh1, 16, "end");
        $free_transaction(trh1);

        /* two overlapping (parallel) transactions */
        #4;                                  /* Idle period                   */
        trh1 =                               /* Start a transaction           */
               $begin_transaction(stream1, "Tran");
        $add_attribute(trh1, 20, "beg");
        #2;
        trh2 =                               /* Start another transaction     */
               $begin_transaction(stream1, "Tran");
        $add_attribute(trh2, 22, "beg");
        #2;
        $end_transaction(trh1);              /* End the first transaction     */
        $add_attribute(trh1, 24, "end");
        $free_transaction(trh1);
        #2;
        $end_transaction(trh2);              /* End the second transaction    */
        $add_attribute(trh2, 26, "end");
        $free_transaction(trh2);

        /* two retro-active transactions */
        #14;                                 /* Advance time to the future    */
        startTime = 30;
        trh1 =                               /* Start a transaction in the    */
               $begin_transaction(stream1, "Tran", startTime);      /* past   */
        $add_attribute(trh1, 30, "beg");
        endTime = 32;
        $end_transaction(trh1, endTime);     /* end it in the past            */
        $add_attribute(trh1, 32, "end");
        $free_transaction(trh1);
        startTime = 34;
        trh1 =                               /* Start another retro           */
               $begin_transaction(stream1, "Tran", startTime); /* transaction */
        $add_attribute(trh1, 34, "beg");
        endTime = 36;
        $end_transaction(trh1, endTime);     /* end it in the past           */
        $add_attribute(trh1, 36, "end");
        $free_transaction(trh1);

        /* two phase transactions */
        trh1 =                               /* Start a transaction           */
               $begin_transaction(stream2, "Tran");
        $add_attribute(trh1, 40, "beg");
        #2;
        trh2 =                               /* Start a child transaction     */
               $begin_transaction(stream2, "Tran",,trh1);
        $add_attribute(trh2, 42, "beg");
        #2;
        $end_transaction(trh2);              /* End the child transaction     */
        $add_attribute(trh2, 44, "end");
        $free_transaction(trh2);
        #2;
        $end_transaction(trh1);              /* End the original transaction  */
        $add_attribute(trh1, 46, "end");
        $free_transaction(trh1);

        /* two serial, non-overlapping (serial) transactions, different names */
        #4;                                  /* Idle period                   */
        trh1 =                               /* Start a named transaction     */
               $begin_transaction(stream2, "Tran_1a");
        $add_attribute(trh1, 50, "beg");
        #2;
        $end_transaction(trh1);              /* End the transaction           */
        $add_attribute(trh1, 52, "end");
        $free_transaction(trh1);
        #2;                                  /* Idle period                   */
        trh1 =                               /* Start another named           */
               $begin_transaction(stream2, "Tran_1b");         /* transaction */
        $add_attribute(trh1, 54, "beg");
        #2
        $end_transaction(trh1);              /* End the transaction           */
        $add_attribute(trh1, 56, "end");
        $free_transaction(trh1);

        /* two overlapping (parallel) transactions, different names */
        #4;                                  /* Idle period                   */
        trh1 =                               /* Start a named transaction     */
               $begin_transaction(stream2, "Tran_1a");
        $add_attribute(trh1, 60, "beg");
        #2;
        trh2 =                               /* Start another transaction     */
               $begin_transaction(stream2, "Tran_1b");
        $add_attribute(trh2, 62, "beg");
        #2;
        $end_transaction(trh1);              /* End the first transaction     */
        $add_attribute(trh1, 64, "end");
        $free_transaction(trh1);
        #2;
        $end_transaction(trh2);              /* End the second transaction    */
        $add_attribute(trh2, 66, "end");
        $free_transaction(trh2);
    end

endmodule
