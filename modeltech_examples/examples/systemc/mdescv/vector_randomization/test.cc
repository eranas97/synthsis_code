#include "scv.h"
#include "packet_ext.h"

using namespace std;

// nbcode "def" start
//create a constraint class
struct addr_constraint : public scv_constraint_base {
  //create the objects that will be constrained
  scv_smart_ptr<int> row;
  scv_smart_ptr<int> col;
  scv_smart_ptr<vector<packet_t> > packvec;

  SCV_CONSTRAINT_CTOR(addr_constraint) {
    string tmp = string(get_name()) + ".row";
    row->set_name(tmp.c_str());
    tmp = string(get_name()) + ".col";
    col->set_name(tmp.c_str());
    tmp = string(get_name()) + ".packvec";
    packvec->set_name(tmp.c_str());

    packvec->vector_size.keep_only(50,100);

    (*packvec)[0].msg_length.keep_only(10,50);
    (*packvec)[0].frame.src_addr.keep_only(10,1000);
    (*packvec)[0].frame.dest_addr.keep_only(10,1000);
    for (int i=0; i<16; ++i) {
      //make the msg alpha numeric
      (*packvec)[0].msg[i] = '\0';

      //you can use keep_only/keep_out only if the element you
      //are constraining is NOT involved in SCV_CONSTRAINTS in
      //any way. In this case, msg is independent of other things.
      (*packvec)[0].msg[i].keep_only(' ', 'z');  //ascii space to z
      (*packvec)[0].msg[i].keep_out('!', '/');   //punctuation characters
      (*packvec)[0].msg[i].keep_out(':', '@');   //more special characters
      (*packvec)[0].msg[i].keep_out('[', '`');   //more special characters
    }

    //soft constraint on row to be between 10 and 50 exclusive or
    //between 200 and 250 inclusive
    SCV_SOFT_CONSTRAINT ( (row() >   10 && row() <   50)  || 
                          (row() >= 200 && row() <= 250) );

    //hard constraint on row to be between the min and max
    //values in the soft constraint, eg, between 10 and 250
    SCV_NAMED_CONSTRAINT ( scv_constraint_expr::HARD, "myconst3", (row() > 10) && (row() <= 250) );

    //hard constraint on col betwen row-5 and row+20
    SCV_NAMED_CONSTRAINT ( scv_constraint_expr::HARD, "myconst1", col() > ( row() - 2) );
    SCV_NAMED_CONSTRAINT ( scv_constraint_expr::HARD, "myconst2",  col() < ( row() + 20) );
    cout << "CONSTRUCTOR" << endl;
  }
};

// nbcode "def" end
SC_MODULE(sctop) {

  SC_CTOR(sctop) {
    scv_random::set_global_seed(0xCCCC);

    //instantiate a constrained object
    addr_constraint addr("addr");

    cout << "DISABLING CONSTRAINT 'myconst2' :: " << addr.disable_constraint("myconst2") << endl;

    //disable randomization on col
    addr.col->disable_randomization();

    //enable randomization on vector_size
    addr.packvec->vector_size.enable_randomization();

    //set value on col, and randomize the object 5 times
    int i, j;
    for(i=25, j=0; i<250; i+=50, ++j) {
      *(addr.col) = i;
      addr.next();
      scv_out << addr.row->get_name() << " = " << *(addr.row) << "\n"
              << addr.col->get_name() << " = " << *(addr.col) << "\n"
              << addr.packvec->get_name() << ".vector_size()" << " = " << addr.packvec->vector_size.get_unsigned() << "\n" << endl;
      int size = addr.packvec->vector_size.get_unsigned();

      for (int j=0; j < 5; j++) {
        cout << addr.packvec->get_name() << "[" << j << "] = " << (*(addr.packvec))[j] << "\n";
      }

      cout << " .... " << endl;

      for (int j=size-5; j < size; j++) {
        cout << addr.packvec->get_name() << "[" << j << "] = " << (*(addr.packvec))[j] << "\n";
      }
      cout << endl;
    }
    scv_out << endl;
  }
};

SC_MODULE_EXPORT(sctop);
