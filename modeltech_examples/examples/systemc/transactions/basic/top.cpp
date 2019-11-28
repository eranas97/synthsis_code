#include <systemc.h>
#include <scv.h>

typedef scv_tr_generator<int, int> generator;

SC_MODULE(tx)
{
    public:
    scv_tr_db        *txdb;
    scv_tr_stream    *stream1, *stream2;
    generator        *gen1, *gen2;

    SC_CTOR(tx)
    {
        SC_THREAD(thread);
    }

    /* initialize transaction recording, create one new transaction */
    /* database, two new transaction streams, and two new generators */
	void initialize(void) {
        scv_startup();
        scv_tr_wlf_init();
        txdb = new scv_tr_db("txdb");
        stream1 = new scv_tr_stream("Stream1", "** TRANSACTOR 1 **", txdb);
        stream2 = new scv_tr_stream("Stream2", "** TRANSACTOR 2 **", txdb);
        gen1 = new generator("Generator", *stream1, "beg", "end");
        gen2 = new generator("Generator", *stream2, "beg", "end");
    }

    void thread(void) {
        initialize();
        sc_time startTime, endTime;
        scv_tr_handle trh1, trh2, trh1a, trh1b;

        /* two serial, non-overlapping (serial) transactions */
        wait(10, SC_NS);                     /* Idle period                   */
        trh1 = gen1->begin_transaction(10);  /* Start a transaction           */
        wait(2, SC_NS);
        gen1->end_transaction(trh1, 12);     /* End the transaction           */
        wait(2, SC_NS);                      /* Idle period                   */
        trh1 = gen1->begin_transaction(14);  /* Start another transaction     */
        wait(2, SC_NS);
        gen1->end_transaction(trh1, 16);     /* End the second transaction    */

        /* two overlapping (parallel) transactions */
        wait(4, SC_NS);                      /* Idle period                   */
        trh1 = gen1->begin_transaction(20);  /* Start a transaction           */
        wait(2, SC_NS);
        trh2 = gen1->begin_transaction(22);  /* Start another transaction     */
        wait(2, SC_NS);
        gen1->end_transaction(trh1, 24);     /* End the first transaction     */
        wait(2, SC_NS);
        gen1->end_transaction(trh2, 26);     /* End the second transaction    */

        /* two retro-active transactions */
        wait(14, SC_NS);                     /* Advance time to the future   */
        startTime = sc_time(30, SC_NS);
        endTime =   sc_time(32, SC_NS);
        trh1 = gen1->begin_transaction(30, startTime); /* Start a transaction*/
                                                       /*   in the past      */
        gen1->end_transaction(trh1, 32, endTime);      /* end it in the past */
        startTime = sc_time(34, SC_NS);
        endTime =   sc_time(36, SC_NS);
        trh1 = gen1->begin_transaction(34, startTime); /* Start another retro*/
                                                       /*   transaction      */
        gen1->end_transaction(trh1, 36, endTime);      /* end it in the past */

        /* two phase transactions */
        trh1 = gen2->begin_transaction(40);  /* Start a transaction           */
        wait(2, SC_NS);
        trh2 = gen2->begin_transaction(42, "mti_phase", trh1);
                                             /* Start a child transaction     */
        wait(2, SC_NS);
        gen2->end_transaction(trh2, 44);     /* End the child transaction     */
        wait(2, SC_NS);
        gen2->end_transaction(trh1, 46);     /* End the original transaction  */

        /* two serial, non-overlapping (serial) transactions, different names */
        generator *gen1a = new generator("Tran_1a", *stream2, "beg", "end");
        generator *gen1b = new generator("Tran_1b", *stream2, "beg", "end");
        wait(4, SC_NS);                      /* Idle period                   */
        trh1a = gen1a->begin_transaction(50);/* Start a named transaction     */
        wait(2, SC_NS);
        gen1a->end_transaction(trh1a, 52);   /* End the transaction           */
        wait(2, SC_NS);                      /* Idle period                   */
        trh1b = gen1b->begin_transaction(54);/* Start a named transaction     */
        wait(2, SC_NS);
        gen1b->end_transaction(trh1b, 56);   /* End the transaction           */

        /* two overlapping (parallel) transactions, different names */
        wait(4, SC_NS);                      /* Idle period                   */
        trh1a = gen1a->begin_transaction(60);/* Start a named transaction     */
        wait(2, SC_NS);
        trh1b = gen1b->begin_transaction(62);/* Start another transaction     */
        wait(2, SC_NS);
        gen1a->end_transaction(trh1a, 64);   /* End the first transaction     */
        wait(2, SC_NS);
        gen1b->end_transaction(trh1b, 66);   /* End the second transaction    */
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
