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
        variable tr1 : TrTransaction := 0;
        variable tr2 : TrTransaction := 0;

        variable i : integer := 0;
        variable t : time := 0 ns;
	begin
        -- two serial, non-concurrent transactions 
        tr1 := begin_transaction(stream,"Ser1");
        add_attribute(tr1, i, "beg");
        i := i + 1;
        t := t + 1 ns;
        wait for 1 ns;
        add_attribute(tr1, i, "end");
        end_transaction(tr1);
        free_transaction(tr1);
        i := i + 1;
        t := t + 1 ns;
        wait for 1 ns;

        tr1 := begin_transaction(stream,"Ser2");
        add_attribute(tr1, i, "beg");
        i := i + 1;
        t := t + 1 ns;
        wait for 1 ns;
        add_attribute(tr1, i, "end");
        end_transaction(tr1);
        free_transaction(tr1);
        i := i + 1;
        t := t + 1 ns;
        wait for 1 ns;

        -- two concurrent (parallel) transactions 
        tr1 := begin_transaction(stream,"Par1");
        tr2 := begin_transaction(stream,"Par2");
        add_attribute(tr1, i, "beg");
        add_attribute(tr2, i, "beg");
        i := i + 1;
        t := t + 1 ns;
        wait for 1 ns;
        add_attribute(tr1, i, "end");
        add_attribute(tr2, i, "end");
        end_transaction(tr1);
        end_transaction(tr2);
        free_transaction(tr1);
        free_transaction(tr2);
        i := i + 1;
        t := t + 1 ns;
        wait for 1 ns;

        -- two retro-active transactions 
        wait for 4 ns; -- advance time first

        tr1 := begin_transaction(stream,"Retro1",t);
        add_attribute(tr1, i, "beg");
        i := i + 1;
        t := t + 1 ns;
        add_attribute(tr1, i, "end");
        end_transaction(tr1, t);
        free_transaction(tr1);
        i := i + 1;
        t := t + 1 ns;

        tr1 := begin_transaction(stream,"Retro2",t);
        add_attribute(tr1, i, "beg");
        i := i + 1;
        t := t + 1 ns;
        add_attribute(tr1, i, "end");
        end_transaction(tr1, t);
        free_transaction(tr1);
        i := i + 1;
        t := t + 1 ns;

        -- a phase transaction
        tr1 := begin_transaction(stream,"Parent");
        tr2 := begin_transaction(stream,"Child", tr1);
        add_attribute(tr1, i, "beg");
        add_attribute(tr2, i, "beg");
        i := i + 1;
        t := t + 1 ns;
        wait for 1 ns;
        add_attribute(tr1, i, "end");
        add_attribute(tr2, i, "end");
        end_transaction(tr2);
        free_transaction(tr2);
        end_transaction(tr1);
        free_transaction(tr1);
        i := i + 1;
        t := t + 1 ns;
        wait for 1 ns;

	end process;

end;

