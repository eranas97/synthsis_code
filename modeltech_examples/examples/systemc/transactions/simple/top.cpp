#include <systemc.h>
#include <scv.h>

typedef scv_tr_generator<int, int> generator;

SC_MODULE(tx)
{
    public:
    scv_tr_db        *txdb;            /* a handle to a transaction database  */
    scv_tr_stream    *stream;          /* a handle to a transaction stream    */
    generator        *gen;             /* a handle to a transaction generator */

    SC_CTOR(tx)
    {
        SC_THREAD(thread);
    }

    /* initialize transaction recording, create one new transaction */
    /* database and one new transaction stream */
	void initialize(void) {
        scv_startup();
        scv_tr_wlf_init();
        txdb = new scv_tr_db("txdb");
        stream = new scv_tr_stream("Stream", "** TRANSACTOR **", txdb);
    }

    /* create one new transaction */
    void thread(void) {
        scv_tr_handle trh;

	    initialize();
        gen = new generator("Generator", *stream, "begin", "end");

        wait(10, SC_NS);                     /* Idle period         */
        trh = gen->begin_transaction(10);    /* Start a transaction */
        wait(2, SC_NS);
        trh.record_attribute("special", 12); /* Add an attribute    */
        wait(2, SC_NS);
        gen->end_transaction(trh, 14);       /* End a transaction   */
        wait(2, SC_NS);                      /* Idle period         */
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
