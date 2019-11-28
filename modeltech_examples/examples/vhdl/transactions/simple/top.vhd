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
        variable tr: TrTransaction := 0;

        variable i : integer := 0;
	begin
        tr := begin_transaction(stream,"Tran1");
        add_attribute(tr, i, "beg");
        i := i + 1;
        wait for 1 ns;
        add_attribute(tr, i, "special");
        i := i + 1;
        wait for 1 ns;
        add_attribute(tr, i, "end");
        end_transaction(tr);
        free_transaction(tr);
        i := i + 1;
        wait for 1 ns;
	end process;

end;

