
// this code compiles and runs with our latest prototype for this specification

#include "scv.h"

// hack to fake a true fifo_mutex
#define fifo_mutex sc_mutex

const unsigned ram_size = 256;


class rw_task_if : virtual public sc_interface {
public:
   typedef sc_uint<8> addr_t;
   typedef sc_uint<8> data_t;
   struct write_t {
     addr_t addr;
     data_t data;
   };

   virtual data_t read(const addr_t*) = 0;
   virtual void write(const write_t*) = 0;
};

SCV_EXTENSIONS(rw_task_if::write_t) {
public:
   scv_extensions<rw_task_if::addr_t> addr;
   scv_extensions<rw_task_if::data_t> data;
   SCV_EXTENSIONS_CTOR(rw_task_if::write_t) {
#ifdef MTI_SYSTEMC
   if (!mti_IsVoptMode())
#endif
     scv_out << "Constructing write_t" << endl;
     SCV_FIELD(addr);
     SCV_FIELD(data);
   }
};

class pipelined_bus_ports : public sc_module {
public:
   sc_in< bool > clk;
   sc_inout< bool > rw;
   sc_inout< bool > addr_req;
   sc_inout< bool > addr_ack;
   sc_inout< sc_uint<8> > bus_addr;
   sc_inout< bool > data_rdy;
   sc_inout< sc_uint<8> > bus_data;

   SC_CTOR(pipelined_bus_ports)
     : clk("clk"), rw("rw"),
       addr_req("addr_req"),
       addr_ack("addr_ack"), 
       bus_addr("bus_addr"),
       data_rdy("data_rdy"), 
       bus_data("bus_data") {
#ifdef MTI_SYSTEMC
       if (!mti_IsVoptMode())
#endif
         scv_out << "Constructing pipelined_bus_ports" << endl;
       }
};

class rw_pipelined_transactor
   : public rw_task_if,
     public pipelined_bus_ports {

   fifo_mutex addr_phase;
   fifo_mutex data_phase;

   scv_tr_stream pipelined_stream;
   scv_tr_stream addr_stream;
   scv_tr_stream data_stream;

   scv_tr_generator<sc_uint<8>, sc_uint<8> > read_gen;
   scv_tr_generator<sc_uint<8>, sc_uint<8> > write_gen;

   scv_tr_generator<sc_uint<8> > addr_gen;
   scv_tr_generator<sc_uint<8>, sc_uint<8> > data_gen;

public:
   rw_pipelined_transactor(sc_module_name nm) :
       pipelined_bus_ports(nm),

       addr_phase("addr_phase"),
       data_phase("data_phase"),

       pipelined_stream("pipelined_stream", "xtransactor"),
       addr_stream("addr_stream", "xtransactor"),
       data_stream("data_stream", "xtransactor"),

        read_gen("read",  pipelined_stream, "addr", "data"),
       write_gen("write", pipelined_stream, "addr", "data"),

       addr_gen("addr", addr_stream, "addr"),
       data_gen("data", data_stream, "data", "data")
   {
#ifdef MTI_SYSTEMC
     if (!mti_IsVoptMode())
#endif
       scv_out << "Constructing rw_pipelined_transactor" << endl;
   }
   virtual data_t read(const addr_t* p_addr);
   virtual void write(const write_t * req);
};

rw_task_if::data_t rw_pipelined_transactor::read(
   const rw_task_if::addr_t* addr) {

   scv_tr_handle h = read_gen.begin_transaction(*addr);

       addr_phase.lock();
       scv_tr_handle h1 = addr_gen.begin_transaction(*addr,"addr_phase",h);
       wait(clk->posedge_event());
       bus_addr = *addr;
       addr_req = 1;
       wait(addr_ack->posedge_event());
       wait(clk->negedge_event());
       addr_req = 0;
       wait(addr_ack->negedge_event());
       addr_gen.end_transaction(h1);
       addr_phase.unlock();

       data_phase.lock();
       scv_tr_handle h2 = data_gen.begin_transaction("data_phase",h);
       wait(data_rdy->posedge_event());
       data_t data = bus_data.read();
       wait(data_rdy->negedge_event());
       data_gen.end_transaction(h2, data);
       data_phase.unlock();

   read_gen.end_transaction(h,data);

   return data;
} 

void rw_pipelined_transactor::write(const write_t * req) {
   scv_tr_handle h = write_gen.begin_transaction(req->addr);

       addr_phase.lock();
       scv_tr_handle h1 = addr_gen.begin_transaction(req->addr,"addr_phase",h);
       wait(clk->posedge_event());
       bus_addr = req->addr;
       addr_req = 1;
       wait(addr_ack->posedge_event());
       wait(clk->negedge_event());
       addr_req = 0;
       wait(addr_ack->negedge_event());
       addr_gen.end_transaction(h1);
       addr_phase.unlock();

       data_phase.lock();
       scv_tr_handle h2 = data_gen.begin_transaction("data_phase",h);
       wait(data_rdy->posedge_event());
       bus_data.write(req->data);
       wait(data_rdy->negedge_event());
       data_gen.end_transaction(h2);
       data_phase.unlock();

   write_gen.end_transaction(h,req->data);
}


class test : public sc_module {
public:
   sc_port< rw_task_if > my_transactor;
   SC_CTOR(test) {
#ifdef MTI_SYSTEMC
     if (!mti_IsVoptMode())
#endif
     scv_out << "Constructing test" << endl;
     SC_THREAD(main);
   }
   void main();
};

inline void test::main() {
   // simple sequential tests
   for (int i=0; i<3; i++) {
     rw_task_if::addr_t addr = i;
     rw_task_if::data_t data = my_transactor->read(&addr);
     cout << "at time " << sc_time_stamp() << ": ";
     cout << "received data : " << data << endl;
   }

   scv_smart_ptr<rw_task_if::addr_t> addr;
   for (int i=0; i<3; i++) {
     addr->next();
     rw_task_if::data_t data = my_transactor->read( addr->get_instance() );
     cout << "data for address " << *addr << " is " << data << endl;
   }

   scv_smart_ptr<rw_task_if::write_t> write;
   for (int i=0; i<3; i++) {
     write->next();
     my_transactor->write( write->get_instance() );
     cout << "send data : " << write->data << endl;
   }

// sc_stop();
}

class design : public pipelined_bus_ports {
   list< sc_uint<8> > outstandingAddresses;
   list< bool > outstandingType;
   sc_uint<8>  memory[ram_size];

public:
   SC_HAS_PROCESS(design);
   design(sc_module_name nm) : pipelined_bus_ports(nm) {
#ifdef MTI_SYSTEMC
     if (!mti_IsVoptMode())
#endif
     scv_out << "Constructing design" << endl;
     for (unsigned i=0; i<ram_size; ++i) { memory[i] = i + 100; }
     SC_THREAD(addr_phase);
     SC_THREAD(data_phase);
     SC_THREAD(clk_watcher);
   }
   void addr_phase();
   void data_phase();
   void clk_watcher();
};

inline void design::clk_watcher() {
   while (1) {
     wait(clk->posedge_event());
     cout << "posedge clk at time " << sc_time_stamp() << endl;
   }
}

inline void design::addr_phase() {

     // int cycle = rand() % 10 + 1;
     int cycle = 0; 
     int cycle_count= 0;
   while (1) {

     while (addr_req.read() != 1) {
       wait(addr_req->value_changed_event());
     }
     sc_uint<8> _addr = bus_addr.read();
     bool _rw = rw.read();

     if (cycle_count++ > 10) 
     cycle_count = 0;
     cycle = cycle_count;
     cout << "cycle = " << cycle << endl;
     while (cycle-- > 0) {
       wait(clk->posedge_event());
     }

     addr_ack = 1;
     wait(clk->posedge_event());
     addr_ack = 0;

     outstandingAddresses.push_back(_addr);
     outstandingType.push_back(_rw);
     cout << "at time " << sc_time_stamp() << ": ";
     cout << "received request for memory address " << _addr << endl;
   }
}

inline void design::data_phase() {

     // int cycle = rand() % 10 + 1;
     int cycle = 0; 
     int cycle_count = 0;
   while (1) {

     while (outstandingAddresses.empty()) {
       wait(clk->posedge_event());
     }
     if (cycle_count++ > 10) 
     cycle_count = 0;
     cycle = cycle_count;
     while (cycle-- > 0) {
       wait(clk->posedge_event());
     }
     if (outstandingType.front() == 0) {
       cout << "reading memory address " << outstandingAddresses.front()
            << " with value " << memory[outstandingAddresses.front()] << endl;
       bus_data = memory[outstandingAddresses.front()];
       data_rdy = 1;
       wait(clk->posedge_event());
       data_rdy = 0;

     } else {
       cout << "not implemented yet" << endl;
     }
     outstandingAddresses.pop_front();
     outstandingType.pop_front();
   }
}

#ifdef SYSTEMC_ORIG
int sc_main (int argc , char *argv[])
{
   scv_startup();

   scv_tr_text_init();
   scv_tr_db db("my_db");
   scv_tr_db::set_default_db(&db);

   // create signals
   sc_clock clk("clk",20, SC_NS,0.5,0, SC_NS,true);
   sc_signal< bool > rw;
   sc_signal< bool > addr_req;
   sc_signal< bool > addr_ack;
   sc_signal< sc_uint<8> > bus_addr;
   sc_signal< bool > data_rdy;
   sc_signal< sc_uint<8> > bus_data;

   // create modules/channels
   test t("t");
   rw_pipelined_transactor tr("tr");
   design duv("duv");

   // connect them up
   t.my_transactor(tr);

   tr.clk(clk);
   tr.rw(rw);
   tr.addr_req(addr_req);
   tr.addr_ack(addr_ack);
   tr.bus_addr(bus_addr);
   tr.data_rdy(data_rdy);
   tr.bus_data(bus_data);

   duv.clk(clk);
   duv.rw(rw);
   duv.addr_req(addr_req);
   duv.addr_ack(addr_ack);
   duv.bus_addr(bus_addr);
   duv.data_rdy(data_rdy);
   duv.bus_data(bus_data);

   // run the simulation
   sc_start(1000000);

   return 0;
}
#else

scv_tr_db *pdb;

// Interface:
//
#ifdef __cplusplus
extern "C" {
#endif /* __cplusplus */

#ifdef __cplusplus
}
#endif /* __cplusplus */

class my_startup : public sc_module {
public:
   SC_CTOR(my_startup) {
#ifdef MTI_SYSTEMC
     if (!mti_IsVoptMode())
#endif
     scv_out << "Constructing my_startup" << endl;
     scv_startup();
#ifdef MTI_SYSTEMC
     scv_tr_wlf_init();
#else
     scv_tr_text_init();
#endif /* MTI_TR */

     pdb = new scv_tr_db("my_db");
     scv_tr_db::set_default_db(pdb);
   }
};

SC_MODULE(top)
{
   // create signals
   sc_clock clk;
   sc_signal< bool > rw;
   sc_signal< bool > addr_req;
   sc_signal< bool > addr_ack;
   sc_signal< sc_uint<8> > bus_addr;
   sc_signal< bool > data_rdy;
   sc_signal< sc_uint<8> > bus_data;

   // create modules/channels
   my_startup s;
   test t;
   rw_pipelined_transactor tr;
   design duv;

   SC_CTOR(top):
       clk("clk",20, SC_NS,0.5,0, SC_NS,true),
       s("s"),
       t("t"),
       tr ("tr"),
       duv("duv")
   {
#ifdef MTI_SYSTEMC
     if (!mti_IsVoptMode())
#endif
       scv_out << "Constructing transactions" << endl;

       // connect them up
       t.my_transactor(tr);

       tr.clk(clk);
       tr.rw(rw);
       tr.addr_req(addr_req);
       tr.addr_ack(addr_ack);
       tr.bus_addr(bus_addr);
       tr.data_rdy(data_rdy);
       tr.bus_data(bus_data);

       duv.clk(clk);
       duv.rw(rw);
       duv.addr_req(addr_req);
       duv.addr_ack(addr_ack);
       duv.bus_addr(bus_addr);
       duv.data_rdy(data_rdy);
       duv.bus_data(bus_data);
   }
};

SC_MODULE_EXPORT(top);

#endif /* SYSTEMC_ORIG */

