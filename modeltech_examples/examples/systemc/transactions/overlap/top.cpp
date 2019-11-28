#include <systemc.h>
#include <scv.h>

typedef scv_tr_generator<int, int> generator;

/* initialize transaction recording, create one new transaction database */
static scv_tr_db *
init_txdb(const char *dbName) {
    static bool dbIsInitialized = false;
    if (!dbIsInitialized) {
        scv_startup();
        scv_tr_wlf_init();
        dbIsInitialized = true;
    }
    scv_tr_db *txdb;
    txdb = new scv_tr_db(dbName);
    return txdb;
}


SC_MODULE(tx)
{
    public:
    scv_tr_db        *txdb;
    scv_tr_stream    *stream;
    generator        *gen;

    SC_CTOR(tx)
    {
        SC_THREAD(thread);
    }

	void initialize(void) {
        txdb = init_txdb("txdb");
        stream = new scv_tr_stream("Stream", "** TRANSACTOR **", txdb);
    }

    void thread(void) {
        scv_tr_handle trh1a, trh1b, trh1c, trh1d, trh2a, trh2b, trh2c, trh2d;

	    initialize();

        /* overlapping phase transactions, different names */
        wait(4, SC_NS); /* Idle period, with no activity. */
        gen = new generator("Tran_1a", *stream, "beg", "end");
        trh1a = gen->begin_transaction(4);
        wait(2, SC_NS);
        gen = new generator("Tran_1b", *stream, "beg", "end");
        trh1b = gen->begin_transaction(6, "mti_phase", trh1a);
        wait(2, SC_NS);
        gen = new generator("Tran_1c", *stream, "beg", "end");
        trh1c = gen->begin_transaction(8, "mti_phase", trh1b);
        gen = new generator("Tran_1d", *stream, "beg", "end");
        trh1d = gen->begin_transaction(8, "mti_phase", trh1c);
        gen = new generator("Tran_2a", *stream, "beg", "end");
        trh2a = gen->begin_transaction(8);
        wait(2, SC_NS);
        gen->end_transaction(trh1d, 10);
        gen = new generator("Tran_2b", *stream, "beg", "end");
        trh2b = gen->begin_transaction(10, "mti_phase", trh2a);
        wait(2, SC_NS);
        gen->end_transaction(trh1c, 12);
        gen = new generator("Tran_2c", *stream, "beg", "end");
        trh2c = gen->begin_transaction(12, "mti_phase", trh2b);
        gen = new generator("Tran_2d", *stream, "beg", "end");
        trh2d = gen->begin_transaction(12, "mti_phase", trh2c);
        wait(2, SC_NS);
        gen->end_transaction(trh1b, 14);
        gen->end_transaction(trh1a, 14);
        gen->end_transaction(trh2d, 14);
        wait(2, SC_NS);
        gen->end_transaction(trh2c, 16);
        wait(2, SC_NS);
        gen->end_transaction(trh2b, 18);
        gen->end_transaction(trh2a, 18);
    }
};

SC_MODULE(top)
{
 public:
  tx *a;
  SC_CTOR(top)
  {
      a = new tx("tx");
  }
};

SC_MODULE_EXPORT(top);
