entity top is
end;

library IEEE;
    use IEEE.std_logic_1164.all;

library modelsim_lib;
    use modelsim_lib.transactions.all;

architecture arch of top is
begin
	process
        variable stream : TrStream := create_transaction_stream("Stream");
        variable tr1a: TrTransaction := 0;
        variable tr1b: TrTransaction := 0;
        variable tr1c: TrTransaction := 0;
        variable tr1d: TrTransaction := 0;

        variable i : integer := 0;
	begin
        tr1a := begin_transaction(stream,"TR1a");
        add_attribute(tr1a, i, "beg");

        i := i + 1;
        wait for 1 ns;
        tr1b := begin_transaction(stream,"Tr1b", tr1a);
        add_attribute(tr1b, i, "beg");

        i := i + 1;
        wait for 1 ns;

        tr1c := begin_transaction(stream,"Tr1c", tr1b);
        add_attribute(tr1c, i, "beg");
        i := i + 1;
        wait for 1 ns;

        tr1d := begin_transaction(stream,"Tr1d", tr1c);
        add_attribute(tr1d, i, "beg");
        i := i + 1;
        wait for 1 ns;

        add_attribute(tr1d, i, "end");
        end_transaction(tr1d, true);
        i := i + 1;
        wait for 1 ns;

        add_attribute(tr1c, i, "end");
        end_transaction(tr1c, true);
        i := i + 1;
        wait for 1 ns;

        add_attribute(tr1b, i, "end");
        end_transaction(tr1b, true);
        i := i + 1;
        wait for 1 ns;

        add_attribute(tr1a, i, "end");
        end_transaction(tr1a, true);
	end process;

end;

