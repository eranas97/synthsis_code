entity top is
end;

library IEEE;
    use IEEE.std_logic_1164.all;

library modelsim_lib;
    use modelsim_lib.transactions.all;

architecture arch of top is
begin
	process
        variable stream1 : TrStream := create_transaction_stream("Stream1");
        variable stream2 : TrStream := create_transaction_stream("Stream2");
        variable stream3 : TrStream := create_transaction_stream("Stream3");
        variable stream4 : TrStream := create_transaction_stream("Stream4");
        variable stream5 : TrStream := create_transaction_stream("Stream5");
        variable tr1: TrTransaction := 0;
        variable tr2: TrTransaction := 0;
        variable tr3: TrTransaction := 0;
        variable tr4: TrTransaction := 0;
        variable tr5: TrTransaction := 0;
	begin
        if (tr1 /= 0) then end_transaction(tr1, true); end if;
        tr1 := begin_transaction(stream1,"TR1");
        wait for 1 ns;

        if (tr2 /= 0) then end_transaction(tr2, true); end if;
        if (tr4 /= 0) then end_transaction(tr4, true); end if;
        tr2 := begin_transaction(stream2,"TR2");
        add_relation(tr2, tr1, "source");
        tr4 := begin_transaction(stream4,"TR4");
        add_relation(tr4, tr1, "source");
        wait for 1 ns;

        if (tr3 /= 0) then end_transaction(tr3, true); end if;
        if (tr5 /= 0) then end_transaction(tr5, true); end if;
        tr3 := begin_transaction(stream3,"TR3");
        add_relation(tr3, tr2, "source");
        tr5 := begin_transaction(stream5,"TR5");
        add_relation(tr5, tr4, "source");
        wait for 1 ns;
	end process;

end;

