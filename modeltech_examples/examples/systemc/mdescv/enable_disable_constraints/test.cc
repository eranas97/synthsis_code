#include "scv.h"

// nbcode "def" start
//create a constraint class
struct addr_constraint : public scv_constraint_base {
  //create the objects that will be constrained
  scv_smart_ptr<int> row;
  scv_smart_ptr<int> col;

  SCV_CONSTRAINT_CTOR(addr_constraint) {
    string tmp = string(get_name()) + ".row";
    row->set_name(tmp.c_str());
    tmp = string(get_name()) + ".col";
    col->set_name(tmp.c_str());

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
    cout << "CALLING CONSTRUCTOR" << endl;
    cout << " DISABLING CONSTRAINT myconst2 :: " << disable_constraint("myconst2") << endl;
  }
};

// nbcode "def" end
SC_MODULE(sctop) {

  SC_CTOR(sctop) {
    scv_random::set_global_seed(0xCCCC);

    //instantiate a constrained object
    addr_constraint addr("addr");

    cout << "is_defined myconst45 (should be 0) :: " << addr.is_defined_constraint("myconst45") << endl;
    cout << "is_defined myconst3 (should be 1) :: " << addr.is_defined_constraint("myconst3") << endl;

    //disable randomization on col
    addr.col->disable_randomization();

    //set value on col, and randomize the object 5 times
    int i, j;
    for(i=25, j=0; i<250; i+=50, ++j) {
      if (j % 2)
        cout << "ENABLING CONSTRAINT myconst2 :: " << addr.enable_constraint("myconst2") << endl;
      else
        cout << "DISABLING CONSTRAINT myconst2 :: " << addr.disable_constraint("myconst2") << endl;

      *(addr.col) = i;
      addr.next();
      scv_out << addr.row->get_name() << " = " << *(addr.row) << "\n"
              << addr.col->get_name() << " = " << *(addr.col) << "\n";

      cout << endl;
    }
    scv_out << endl;
  }
};

SC_MODULE_EXPORT(sctop);
