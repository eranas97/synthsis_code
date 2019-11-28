// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#include "test_constraint.h"

#ifdef MTI_INTEGRATION
  SC_MODULE_EXPORT(sctop);
#endif

static void reportIfFalse(bool ok, const char *message1, const char *message2=NULL) {
  if (ok) {
    if (message2) cout << TBS_INFO << message2 << endl;
  } else {
    assert(message1);
    success = false;
    cout << TBS_INFO << message1 << endl;
    globalTestFailures++;
  }
}

/////////////////////////////////////////////////////
// Class - simple_constraint
//   - Constraint invovling 3 C data type variables.
//   - Limit the values of variables in the constraint
/////////////////////////////////////////////////////
class simple_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<int> val;
  scv_smart_ptr<int> val1;
  scv_smart_ptr<int> val2;
  SCV_CONSTRAINT_CTOR(simple_constraint) {
    SCV_CONSTRAINT(val() >= 1 && val() <= 99);
    SCV_CONSTRAINT(val1() >= 100 && val1() <= 200);
    SCV_CONSTRAINT(val2() >= 200 && val2() <= 300);
  }
};

/////////////////////////////////////////////////////
// Class - constraint2
//   - Constraint invovling 2 C data type variables.
//   - Limit the values of variables in the constraint
//   - Complex constraint involving  the 2 variables
/////////////////////////////////////////////////////
class constraint2 : public scv_constraint_base {
public:
  scv_smart_ptr<int> val;
  scv_smart_ptr<int> val1;
  SCV_CONSTRAINT_CTOR(constraint2) {
    SCV_CONSTRAINT(val() >= 1000 && val() <= 9999);
    SCV_CONSTRAINT(val1() >= 1000 && val1() <= 9999);
    SCV_CONSTRAINT(val() > val1() );
  }
};

/////////////////////////////////////////////////////
// Class - paramertizable constraint
//   - Constraint invovling 2 C data type variables.
//   - Limit the values of variables in the constraint
//   - Change index value at run time to change constraint
//     expression.
/////////////////////////////////////////////////////
class parameterized_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<int> val;
  scv_smart_ptr<int> index;
  SCV_CONSTRAINT_CTOR(parameterized_constraint) {
    SCV_CONSTRAINT(val() >= 1 && val() <= 2);
    SCV_CONSTRAINT(val() != index());
  }

};

//////////////////////////////////////////////////////////////
// COMPOSITE TYPE AND INHERITANCE CONSTRAINTS
//
//////////////////////////////////////////////////////////////
struct packet_t {
  int packet_type;
  int src;
  int dest;
  int payload;
public:
  friend bool operator == (const packet_t& p1, const packet_t& p2);
#if defined (_USE_EXPLICIT_NEQ)
  friend bool operator != (const packet_t& p1, const packet_t& p2);
#endif
};

bool operator == (const packet_t& p1, const packet_t& p2) {
  return (p1.packet_type == p2.packet_type &&
          p1.src == p2.src &&
          p1.dest == p2.dest &&
          p1.payload == p2.payload);
}

#if defined (_USE_EXPLICIT_NEQ)
bool operator != (const packet_t& p1, const packet_t& p2) {
  return (!(operator==(p1,p2)));
}
#endif

ostream& operator<<(ostream& os, const packet_t& p) {
  os << "packet : " << endl;
  os << p.packet_type << endl;
  os << p.src << endl;
  os << p.dest << endl;
  os << p.payload << endl;
  os << "end_packet" << endl;
  return os;
}

template<>
class scv_extensions<packet_t> : public scv_extensions_base<packet_t> {
public:
  scv_extensions<int> packet_type;
  scv_extensions<int> src;
  scv_extensions<int> dest;
  scv_extensions<int> payload;

  SCV_EXTENSIONS_CTOR(packet_t) {
          SCV_FIELD(packet_type);
      SCV_FIELD(src);
      SCV_FIELD(dest);
      SCV_FIELD(payload);
  }
};

class packet_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<packet_t> packet;
  SCV_CONSTRAINT_CTOR( packet_constraint ) {
    SCV_CONSTRAINT( packet->src() != packet->dest() );
    SCV_CONSTRAINT( packet->src() + packet->dest() == 10 );
  }
};

class packet_src_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<packet_t> packet;
  scv_smart_ptr<int> index;

  SCV_CONSTRAINT_CTOR( packet_src_constraint ) {
    SCV_CONSTRAINT( packet->src() != index() );
  }
};

class constraint_a : public scv_constraint_base {
public:
  scv_smart_ptr<packet_t> packet;
  SCV_CONSTRAINT_CTOR( constraint_a ) {
    SCV_CONSTRAINT( packet->src() != packet->dest() );
  }
};

class constraint_ab : virtual public constraint_a {
public:
  SCV_CONSTRAINT_CTOR( constraint_ab ) {
    SCV_BASE_CONSTRAINT(constraint_a);
    SCV_CONSTRAINT( packet->src() + packet->dest() == 10 );
  }
};

class constraint_ac : virtual public constraint_a {
public:
  SCV_CONSTRAINT_CTOR( constraint_ac) {
    SCV_BASE_CONSTRAINT(constraint_a);
    SCV_CONSTRAINT( packet->payload() != 0 );
  }
};

class constraint_abc : public constraint_ab, public constraint_ac {
public:
  SCV_CONSTRAINT_CTOR( constraint_abc ) {
    SCV_BASE_CONSTRAINT(constraint_ab);
    SCV_BASE_CONSTRAINT(constraint_ac);

    SCV_CONSTRAINT( packet->src() < 2 );
  }
};


sctop::sctop(sc_module_name name) : sc_module(name)
{}

int sc_main(int argc, char** argv) {
    sctop top("top");  //for osci
    sc_start();
    return 0;
}

////////////////////////////////////////////////////////
// function: test_basic_class_next
//   - Checks expression creation for constraint class
//   - Checks value generation using var.next() for constraint
//     class objects
////////////////////////////////////////////////////////
void test_basic_class_next(void)
{
  {
    cout << "Test basic constraint creation " << endl;

    simple_constraint a("a");

    cout << "Generate 10 set of 3 values " << endl;
    cout << "Should be [1-100]  [100-200] [200-300] " << endl;

    for (int i=0; i < 10; i++) {
      a.next();
      cout << *a.val << "  " << *a.val1 << "  " << *a.val2 << endl;

      reportIfFalse(*a.val >= 1 && *a.val <= 99, "FAILED- test9");
      reportIfFalse(*a.val1 >= 100 && *a.val1 <= 200, "FAILED- test10");
      reportIfFalse(*a.val2 >= 200 && *a.val2 <= 300, "FAILED- test11");
    }
  }

  cout << "Generate 10 set of 2 values " << endl;
  cout << "Should be [1000-9999]  [1000-9999] && val1 > val2" << endl;
  {
    constraint2 b("b");

    for (int i=0; i < 10; i++) {
      b.next();
      cout << *b.val << "  "  << *b.val1 << endl;
      reportIfFalse(*b.val >= 1000 && *b.val <= 9999, "FAILED- test12");
      reportIfFalse(*b.val > *b.val1, "FAILED- test13");
    }
  }
}

//////////////////////////////////////////////////////////
// function: test_constraint_smart_ptr
//   - Assigns a smart_ptr declared in the test to different
//     smar_ptr's in constraint classes and generate new
//     values based on different constraints.
//////////////////////////////////////////////////////////
void test_constraint_smart_ptr()
{
  {
    cout << "Check generating value from smart_ptr assigned a constrained smart_ptr" << endl;

    simple_constraint a("a");

    scv_smart_ptr<int> my_data;
    my_data = a.val;

    cout << "Set of 10 values [1,99]" << endl;
    for (int i=0; i < 10; i++) {
      my_data->next();
      cout << *my_data << endl;
      reportIfFalse(*my_data >= 1 && *my_data <= 99, "FAILED- test1");
    }

    cout << "Set of 10 values [100,200]" << endl;
    my_data = a.val1;
    for (int i=0; i < 10; i++) {
      my_data->next();
      cout << *my_data << endl;
      reportIfFalse(*my_data >= 100 && *my_data <= 200, "FAILED- test2");
    }

    cout << "Set of 10 values [200,300]" << endl;
    my_data = a.val2;
    for (int i=0; i < 10; i++) {
      my_data->next();
      cout << *my_data << endl;
      reportIfFalse(*my_data >= 200 && *my_data <= 300, "FAILED- test3");
    }
  }

}

/////////////////////////////////////////////////////////////
// function: test_use_constraint
//   - Change constraint at runtime for a smart_ptr
//   - use_constraint method on smart_ptr is th API for that.
/////////////////////////////////////////////////////////////
void test_use_constraint()
{
  {
    cout << "Test use_constraint use model" << endl;

    scv_smart_ptr<int> my_data;
    simple_constraint a("a");
    my_data->use_constraint(a.val);

    cout << "Set of 10 values between [1,99]" << endl;
    for (int i=0; i < 10; i++) {
      my_data->next();
      cout << *my_data << endl;
      reportIfFalse(*my_data >= 1 && *my_data <= 99, "FAILED- test7");
    }

    constraint2 b("b");
    my_data->use_constraint(b.val);
    cout << "Set of 10 values between [1000, 9999] " << endl;
    for (int i=0; i < 10; i++) {
      my_data->next();
      cout << *my_data << endl;
      reportIfFalse(*my_data >= 1000 && *my_data <= 9999, "FAILED- test8");
    }
  }
}

/////////////////////////////////////////////////////////////
// function: test_partial_constraint_initialization
//   - Initialize value of the index
//   - Check the value of the variable constraint a.val
/////////////////////////////////////////////////////////////
void test_partial_constraint_initialization()
{
  {
    scv_smart_ptr<int> my_data;

    parameterized_constraint a("a");

    cout << "Test parameterized constraint class" << endl;
    cout << "Should print set of 10 values in the order 2 followed by 1" << endl;
    for (int j=0; j < 10; j++) {
      for (int i=1; i <= 2; ++i) {
        *a.index = i;
        a.val->next();
        cout << *a.val << endl;
        reportIfFalse(i != *a.val, "FAILED- test6");
      }
      cout << endl;
    }
  }
}


/////////////////////////////////////////////////////////////
// function: test_no_constraint
//   - Check the creation of random value without any other
//   - kind of constraints
/////////////////////////////////////////////////////////////
void test_no_constraint()
{
  cout << "Test generation of random values without constraint" << endl;
  cout << "Should print 10 random values" << endl;

  {
    scv_smart_ptr<int> sp;
    int num[10];

    for (int i=0; i < 10; i++) {
      sp->next();
      cout << *sp << endl;
      num[i] = *sp;
    }
    // NEWTEST: Make sure all of these are not 0's
    int failed = 1;
    for (int i=0; i < 10; i++) {
      failed = (failed && num[i]);
    }
    reportIfFalse(failed, "Failed newtest1");
  }
}

/////////////////////////////////////////////////////////////
// function: test_distribution_constraint
//   - Check a distribution of value created by scv_bag
/////////////////////////////////////////////////////////////
void test_distribution_constriant()
{
  {
    cout << "Check scv_bag distribution mechanism" << endl;
    cout << "Print set of 1000 values from [10|20|30|40]" << endl;
    scv_smart_ptr<int> sp;

    scv_bag<int> dist("dist");
    dist.push(10, 5);
    dist.push(20, 5);
    dist.push(30, 5);
    dist.push(40, 5);

    sp->set_mode(dist);

    int num[4];

    for (int i=0; i < 4; i++) {
      num[i] = 0;
    }

    for (int i=0; i < 1000; i++) {
      sp->next();
      cout << *sp << endl;
      int value = *sp;
      switch(value) {
        case 10:
          num[0]++; break;
        case 20:
          num[1]++; break;
        case 30:
          num[2]++; break;
        case 40:
          num[3]++; break;
        default:
          reportIfFalse(0, "Failed- newtest2");
          break;
      }
    }
    // NEWTEST: Test for equal distribution of values
    reportIfFalse (num[0] >= 200 && num[0] <= 300, "Failed - newtest3");
    reportIfFalse (num[1] >= 200 && num[1] <= 300, "Failed - newtest4");
    reportIfFalse (num[2] >= 200 && num[2] <= 300, "Failed - newtest5");
    reportIfFalse (num[3] >= 200 && num[3] <= 300, "Failed - newtest6");
  }

  {
    scv_bag<pair<int, int> > dist;

    dist.push(pair<int,int>(5,6), 5);
    dist.push(pair<int,int>(7,8), 15);
    dist.push(pair<int,int>(9,10), 80);

    scv_smart_ptr<int> sp;

    sp->set_mode(dist);

    int num[3];

    for (int i=0; i < 3; i++) {
      num[i] = 0;
    }

    for (int i =0; i < 2000; i++) {
      sp->next();
      cout << *sp << endl;
      int value = *sp;

      if (value >=5 && value <=6 ) {
        num[0]++;
      } else if (value >=7 && value <= 8) {
        num[1]++;
      } else if (value >=9 && value <= 10) {
        num[2]++;
      } else {
        reportIfFalse(0, "Failed - newtest7");
      }
    }
    // NEWTEST: Test for distribution
    reportIfFalse( num[0] >=60 && num[0] <=140, "Failed - newtest8");
    reportIfFalse( num[1] >=240 && num[1] <=360, "Failed - newtest9");
    reportIfFalse( num[2] >=1400 && num[2] <=1800, "Failed - newtest10");
  }
}

class constraint_single : public scv_constraint_base {
public:
  scv_smart_ptr<int> sp;
  SCV_CONSTRAINT_CTOR(constraint_single) {
    SCV_CONSTRAINT( sp() >= 1 && sp() <= 5);
  };
};

class constraint_multi : public scv_constraint_base {
public:
  scv_smart_ptr<int> a;
  scv_smart_ptr<int> b;
  SCV_CONSTRAINT_CTOR(constraint_multi) {
    SCV_CONSTRAINT( a() >= 1 && a() <= 5);
    SCV_CONSTRAINT( b() >= 1 && b() <= 5);
    SCV_CONSTRAINT( a() > b() );
  };
};

/////////////////////////////////////////////////////////////
// function: test_avoid_duplicate
//   - Check RANDOM_AVOID_DUPLICATE_MODE
/////////////////////////////////////////////////////////////
void test_avoid_duplicate()
{
  cout << endl;
  cout << "Test RANDOM_AVOID_DUPLICATE_MODE" << endl;
  cout << "Tests this mode setting for constraint classes" << endl;

  {
    cout << endl;
    cout << "Print 3 set of 5 values [1,5]" << endl;
    cout << "Each set of values should not have repetition" << endl;
    constraint_single c("c");
    c.set_mode(scv_extensions_if::RANDOM_AVOID_DUPLICATE);

    int num[5];

    for (int j=0; j < 5; j++) {
      num[j] = 0;
    }

    for (int i=0; i < 15; i++) {
      if ( (i != 0) && i%5==0) {
        int all_one = 1;

        cout << endl;
        for (int j=0; j < 5; j++) {
          all_one = (all_one && (num[j] == 1));
        }
        reportIfFalse(all_one, "Failed newtest11");
        for (int j=0; j < 5; j++) {
          num[j] = 0;
        }
      }
      c.next();
      cout << *c.sp << endl;
      int value = *c.sp;
      reportIfFalse(value >= 1 && value <= 5, "Failed newtest12");
      num[value-1]++;
    }
    cout << endl;
    // NEWTEST: RANDOM_AVOID_DUPLICATE
  }

  {
    cout << endl;
    cout << "Print 3 set of 10 values a>b && a[1,5] && b[1,5]" << endl;
    cout << "Each set of values should not have repetition" << endl;
    constraint_multi c("c");

    int num[10]; // 10 combinations

    for (int j=0; j < 10; j++) {
      num[j] = 0;
    }

    c.set_mode(scv_extensions_if::RANDOM_AVOID_DUPLICATE);
    for (int i=0; i < 30; i++) {
      if ( (i!=0) && i%10==0) {
        int all_one = 1;
        cout << endl;
        for (int j=0; j < 10; j++) {
          all_one = (all_one && (num[j] == 1));
        }
        reportIfFalse(all_one, "Failed newtest13");
        for (int j=0; j < 10; j++) {
          num[j] = 0;
        }
      }
      c.next();
      cout << *c.a << "  " << *c.b << endl;
      int val_a = *c.a;
      int val_b = *c.b;

      reportIfFalse((val_a > val_b), "Failed newtest14");
      if (val_a == 5 && val_b ==4) {
        num[0]++;
      } else if (val_a == 5 && val_b ==3) {
        num[1]++;
      } else if (val_a == 5 && val_b ==2) {
        num[2]++;
      } else if (val_a == 5 && val_b ==1) {
        num[3]++;
      } else if (val_a == 4 && val_b ==3) {
        num[4]++;
      } else if (val_a == 4 && val_b ==2) {
        num[5]++;
      } else if (val_a == 4 && val_b ==1) {
        num[6]++;
      } else if (val_a == 3 && val_b ==2) {
        num[7]++;
      } else if (val_a == 3 && val_b ==1) {
        num[8]++;
      } else if (val_a == 2 && val_b ==1) {
        num[9]++;
      } else {
        reportIfFalse(0, "Failed newtest15");
      }
    }
    cout << endl;
    // NEWTEST: RANDOM_AVOID_DUPLICATE
  }
}

/////////////////////////////////////////////////////////////
// function: test_value_generation_mode
//   - Check a distribution of value created by scv_bag
/////////////////////////////////////////////////////////////
void test_value_generation_mode()
{
  {
    cout << endl;
    cout << "Test SCAN value generation mode" << endl;
    cout << "This has not been implemented yet" << endl;
    scv_smart_ptr<int> sp;
    sp->set_mode(scv_extensions_if::SCAN);
    for (int i=0; i < 10; i++) {
      sp->next();
      cout << *sp << endl;
    }
    // NEWTEST: SCAN with NO constraints and interval of 10
  }
  test_avoid_duplicate();
}

class record_equal_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<packet_t> p1;
  scv_smart_ptr<packet_t> p2;

  SCV_CONSTRAINT_CTOR(record_equal_constraint) {
    SCV_CONSTRAINT(p1() == p2());
  }
};

class pack_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<packet_t> p;
  scv_smart_ptr<int> s;
  SCV_CONSTRAINT_CTOR(pack_constraint) {
    SCV_CONSTRAINT((*s)() >= 1 && (*s)() <= 100);
  }
};

class param_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<int> val;
  scv_smart_ptr<int> lb;
  scv_smart_ptr<int> ub;
  SCV_CONSTRAINT_CTOR(param_constraint) {
    SCV_CONSTRAINT(val() >= lb() && val() <= ub());
  }
};

class equal_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<int> a;
  scv_smart_ptr<int> b;

  SCV_CONSTRAINT_CTOR(equal_constraint) {
    SCV_CONSTRAINT(a() == b());
  }
};

void test_disable_randomization()
{

  // Parameterized constraints
  {
    param_constraint  pc("pc");

    *pc.lb = 5;
    *pc.ub = 10;

    if (pc.lb->is_randomization_enabled()) {
      pc.lb->disable_randomization();
    }

    if (pc.ub->is_randomization_enabled()) {
      pc.ub->disable_randomization();
    }

    cout << "Obtain 10 values between [5,10] using disable_randomization()" << endl;

    for (int i=0; i < 10; i ++) {
      pc.next();
      cout << *pc.val << endl;
      // NEWTEST: Makesure value is between [5, 10]
      int val = *pc.val;
      reportIfFalse(val >=5 && val <=10, "Failed- newtest16");
    }

    *pc.lb = 15;
    *pc.ub = 20;

    cout << "Obtain 10 values between [15,20] using disable_randomization()" << endl;

    for (int i=0; i < 10; i ++) {
      pc.next();
      cout << *pc.val << endl;
      // NEWTEST: Makesure value is between [15, 20]
      int val = *pc.val;
      reportIfFalse(val >=15 && val <=20, "Failed- newtest17");
    }

  }


  cout << endl;

  {
    equal_constraint ec("ec");

    cout << "Print 10 unconstrained values using enable_randomization() and next() on individual elements of dependent streams" << endl;

    for (int i =0; i < 10; i++) {
      ec.b->enable_randomization();
      ec.a->next();
      ec.b->next();

      cout << *ec.a << " : " << *ec.b << endl;
      // NEWTEST: (a == b)
      int val_a = *ec.a;
      int val_b = *ec.b;

      reportIfFalse(val_a == val_b, "Failed - newtest18");
    }
  }

  // Packet constriants
  {
    cout << endl;

    pack_constraint pack_constr("pack_constr");

    cout << "Print unconstrained values for composite type and constrainted for last element " << endl;
    pack_constr.next();
    cout << pack_constr.p->packet_type << endl;
    cout << pack_constr.p->src << endl;
    cout << pack_constr.p->dest << endl;
    cout << pack_constr.p->payload << endl;
    cout << *pack_constr.s << endl;

    packet_t prev_val;

    prev_val.packet_type = pack_constr.p->packet_type;
    prev_val.src = pack_constr.p->src;
    prev_val.dest = pack_constr.p->dest;
    prev_val.payload = pack_constr.p->payload;

    pack_constr.p->disable_randomization();

    cout << endl;

    cout << "Print 10 values where composite element is not being randomized()" << endl;
    for (int i=0; i < 10; i++) {
      pack_constr.next();
      cout << pack_constr.p->packet_type << endl;
      cout << pack_constr.p->src << endl;
      cout << pack_constr.p->dest << endl;
      cout << pack_constr.p->payload << endl;
      cout << *pack_constr.s << endl;
      // NEWTEST: (pack_constr.p == before for loop)
      packet_t curr_val = *pack_constr.p;

      reportIfFalse(curr_val == prev_val, "Failed - newtest19");
      // NEWTEST: (pack_constr.s between [1,100]) and changing
      int val_s = *pack_constr.s;
      reportIfFalse(val_s>=1 && val_s<=100, "Failed-newtest20");
    }

    cout << "Print 10 values where composite element is NOW BEING randomized with enable_randomization()" << endl;
    pack_constr.p->enable_randomization();
    cout << endl;

    for (int i=0; i < 10; i++) {
      pack_constr.next();
      cout << pack_constr.p->packet_type << endl;
      cout << pack_constr.p->src << endl;
      cout << pack_constr.p->dest << endl;
      cout << pack_constr.p->payload << endl;
      cout << *pack_constr.s << endl;
      // NEWTEST: Make sure randomization is now happening

      packet_t curr_val = *pack_constr.p;

      reportIfFalse(curr_val!= prev_val, "Failed - newtest21");
      int val_s = *pack_constr.s;
      reportIfFalse(val_s>=1 && val_s<=100, "Failed-newtest22");
    }

  }

  // Using constraints on existing variables
  {
    equal_constraint ec("ec");

    scv_smart_ptr<int> a;
    scv_smart_ptr<int> b;

    a->use_constraint(ec.a);
    b->use_constraint(ec.b);

    cout << "Print 10 values on existing smart_ptr using enable_randomization() with CONSTRAINT (a == b)" << endl;
    for (int i=0; i < 10; i++) {
      b->enable_randomization();
      a->next();
      b->next();
      cout << *a << " : " << *b << endl;
      // NEWTEST : (a == b)
      int val_a = *a;
      int val_b = *b;
      reportIfFalse(val_a == val_b, "Failed - newtest23");
    }
  }

}


/////////////////////////////////////////////////////////////
// function: test_value_generation_mode
//   - check constraint on composite data types
//   - check constraints based on inheritance
/////////////////////////////////////////////////////////////
void test_composite_constraint() {

  {
    cout << "Obtain value using next on class object" << endl;
    cout << "  - (packet.src + packet.dest == 10) " << endl;
    packet_constraint a("a");
    a.next();
    cout << *a.packet << endl;

    // NEWTEST : Check for packet.src + packet.dest == 10 &&
    // NEWTEST : Check packet.src != packet.dest

    int val_src = a.packet->src;
    int val_dest = a.packet->dest;

    reportIfFalse(val_src+val_dest == 10, "Failed - newtest24");
    reportIfFalse(val_src != val_dest, "Failed - newtest25");
  }

  {
    cout << "Obtain value using next on smart_ptr and use_constraint" << endl;
    cout << "  - (packet.src + packet.dest == 10) " << endl;
    scv_smart_ptr<packet_t> my_data;

    packet_constraint a("a");
    my_data->use_constraint(a.packet);

    cout << "2 set of values satisfying packet_constraint" << endl;
    for (int i=0; i < 2;i++)  {
      my_data->next();

      cout << *my_data << endl;
      // NEWTEST : Check for packet.src + packet.dest == 10 &&
      // NEWTEST : Check packet.src != packet.dest
      int val_src = my_data->src;
      int val_dest = my_data->dest;

      reportIfFalse(val_src+val_dest == 10, "Failed - newtest26");
      reportIfFalse(val_src != val_dest, "Failed - newtest27");
    }
  }

  {
    scv_smart_ptr<packet_t> my_data;

    cout << "Obtain value using next on smart_ptr and use_constraint" << endl;
    cout << "1 set of values satisfying packet_src_constraint" << endl;
    cout << "  - ( packet->src() != (*index)() )" << endl;
    packet_src_constraint a("a");
    my_data->use_constraint(a.packet);
    for (int i=0; i<1; ++i) {
      *a.index = i;
      my_data->next();
      cout << *my_data << endl;
      // NEWTEST : Check for packet.src != index
      int val = my_data->src;
      int index = *a.index;
      reportIfFalse(val != index, "Failed -newtest28");
    }
  }

  {
    scv_smart_ptr<packet_t> my_data;

    cout << "Obtain value using next on smart_ptr and use_constraint" << endl;
    cout << "  constraint_a - ( packet->src() != packet->dest() )" << endl;
    cout << "  constraint_ab - ( packet->src() + packet->dest() == 10 )" << endl;
    cout << "  constraint_ac - ( packet->payload() != 0 )"  << endl;
    cout << "  constraint_abc - ( packet->src() < 2 )" << endl;

    cout << "1 set of values satisfying constraint_ab" << endl;
    constraint_ab c_ab("c_ab");
    //c_ab.packet = my_data;
    my_data->use_constraint(c_ab.packet);
    my_data->next();
    cout << *my_data << endl;
    // NEWTEST: Check for constraint_ab
    int val_src = my_data->src;
    int val_dest =  my_data->dest;
    reportIfFalse(val_src + val_dest == 10, "Failed - newtest29");

    cout << "Obtain value using next on smart_ptr and use_constraint" << endl;
    cout << "1 set of values satisfying constraint_ac" << endl;
    constraint_ac c_ac("c_ac");
    //c_ac.packet = my_data;
    my_data->use_constraint(c_ac.packet);
    my_data->next();
    cout << *my_data << endl;
    int val_payload = my_data->payload;
    reportIfFalse(val_payload != 0, "Failed - newtest30");

    cout << "Obtain value using next on smart_ptr and use_constraint" << endl;
    cout << "1 set of values satisfying constraint_abc" << endl;
    // NEWTEST: Check for constraint_ac


    constraint_abc c_abc("c_abc");
    //c_abc.packet = my_data;
    my_data->use_constraint(c_abc.packet);
    my_data->next();
    cout << *my_data << endl;
    // NEWTEST: CHeck for constraint_abc
    val_src = my_data->src;
    val_dest = my_data->dest;
    val_payload = my_data->payload;

    reportIfFalse(val_src+val_dest == 10, "Failed - newtest31");
    reportIfFalse(val_src < 2, "Failed - newtest32");
    reportIfFalse(val_payload != 0, "Failed - newtest33");
  }

  {
    cout << "Obtain value using next on smart_ptr and use_constraint" << endl;
    cout << "1 set of values satisfying constraint_abc" << endl;
    scv_smart_ptr<packet_t> my_data;

    constraint_abc c_abc("c_abc");
    my_data->use_constraint(c_abc.packet);

    my_data->next();
    cout << *my_data << endl;
    // NEWTEST: Check for constraint_abc
    int val_src = my_data->src;
    int val_dest = my_data->dest;
    int val_payload = my_data->payload;

    reportIfFalse(val_src+val_dest == 10, "Failed - newtest34");
    reportIfFalse(val_src < 2, "Failed - newtest35");
    reportIfFalse(val_payload != 0, "Failed - newtest36");
  }

  {
    scv_smart_ptr<packet_t> pp;
    cout << "Obtain value's along with disable_randomization " << endl;

    pp->packet_type = 0;         // fix packet_type
    pp->src = 3;                 // fix src

    pp->packet_type.disable_randomization();
    pp->src.disable_randomization();

    for (int i = 0; i<5; ++i) {
      pp->next();            // generate random values for dest/payload.
      cout << *pp << endl;
      // NEWTEST: Make sure pp->packet_type == 0 &&
      // NEWTEST: Make sure pp->src == 3 and the rest
      int val_pt = pp->packet_type;
      int val_src = pp->src;
      reportIfFalse(val_pt == 0, "Failed - newtest37");
      reportIfFalse(val_src == 3, "Failed - newtest38");
    }
  }

  {
    cout << "Check constraint on 2 record elements in a constraint" << endl;
    record_equal_constraint rec("rec");

    rec.next();

    cout << rec.p1->packet_type << " " ;
    cout << rec.p1->src << " " ;
    cout << rec.p1->dest << " " ;
    cout << rec.p1->payload << endl;

    cout << rec.p2->packet_type << " " ;
    cout << rec.p2->src << " " ;
    cout << rec.p2->dest << " " ;
    cout << rec.p2->payload << endl;
    // NEWTEST: Make sure (rec.p1 == rec.p2)

    packet_t p1 = *rec.p1;
    packet_t p2 = *rec.p2;

    reportIfFalse(p1 == p2, "Failed - newtest39");
  }

}


class ignore_soft_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<int> a;
  scv_smart_ptr<int> b;
  SCV_CONSTRAINT_CTOR(ignore_soft_constraint) {
    SCV_CONSTRAINT( a() >= 1 && a() <= 10);
    SCV_CONSTRAINT( b() >= 20 && b() <= 30);
    SCV_SOFT_CONSTRAINT(a() == b());
  };
};

class ignore_hard_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<int> a;
  scv_smart_ptr<int> b;
  SCV_CONSTRAINT_CTOR(ignore_hard_constraint) {
    SCV_CONSTRAINT( a() == b() );
    SCV_CONSTRAINT( a() != b() );
  };
};

class ignore_soft_constraint_runtime : public scv_constraint_base {
public:
  scv_smart_ptr<int> a;
  scv_smart_ptr<int> b;
  SCV_CONSTRAINT_CTOR(ignore_soft_constraint_runtime) {
    SCV_CONSTRAINT( a() >= 1 && a() <= 10);
    SCV_CONSTRAINT( b() >= 5 && b() <= 15);
    SCV_SOFT_CONSTRAINT(a() == b());
  };
};

/////////////////////////////////////////////////////////////
// function: test_over_constrained
//   - check ignoring soft constraints
//   - check ignoring hard constraints
/////////////////////////////////////////////////////////////
void test_over_constrained_objects()
{
  unsigned hold = scv_report_handler::force(SCV_CACHE_REPORT);

  {
    cout <<  "************************START TEST *******************" << endl <<  endl;
    ignore_soft_constraint c("c");

    cout << "Ignore soft constraint a == b " << endl;
    cout << "Print a WARNING message about ignoring soft constraint" << endl;
    cout << "Generate set of 10 values a[1,10]  b[20,30]" << endl;
    // Error message about ignoring soft constraint
    // printed only once

    // NEWTEST: Check for a WARNING once
    if (scv_report_handler::get_cached_report() == NULL) {
      reportIfFalse(0, "Failed - newtest40");
    } else {
      scv_report_handler::clear_cached_report();
    }

    for (int i=0; i < 10; i++) {
      c.next();

      cout << *c.a << "  "  << *c.b << endl;
    }
    cout <<  "************************END TEST *******************" << endl <<  endl;
  }

  {
    cout <<  "************************START TEST *******************" << endl <<  endl;
    ignore_hard_constraint c("c");

    cout << "Print ERROR for not being able to satisfy hard constraint" << endl;
    cout << "Print set of 10 unconstrained values " << endl;
    // Ignore all hard constraint a == b
    // Error message about ignoring hard constraint
    // printed only once
    if (scv_report_handler::get_cached_report() == NULL) {
      reportIfFalse(0, "Failed - newtest41");
    } else {
      scv_report_handler::clear_cached_report();
    }
    for (int i=0; i < 10; i++) {
      c.next();

      cout << *c.a << "  "  << *c.b << endl;
      // NEWTEST: Check for an ERROR once
    }
    cout << endl;
    cout <<  "************************END TEST *******************" << endl <<  endl;
  }

  {
    cout <<  "************************START TEST *******************" << endl <<  endl;
    ignore_soft_constraint_runtime c("c");

    cout << "Should generate 10 values [5,10] && (a==b)" << endl;
    for (int i=0; i < 10; i++) {
      c.next();
      cout << *c.a << "  " << *c.b << endl;
    }
    cout << endl;

    cout << "Ignore soft constraint a == b at runtime " << endl;
    cout << "Print a WARNING about ignoring soft constraint" << endl;
    cout << "Second value on each line should be 12" << endl;
    // This will get ignored because of the assignment to b
    // Error message about ignoring soft constraint
    // printed only once
    *c.b  = 12;
    cout << *c.a << "  " << *c.b << endl;

    for (int i=0; i < 9; i++) {
      c.a->next();
      cout << *c.a << "  " << *c.b << endl;

    }
    // NEWTEST: Get WARNING once
    if (scv_report_handler::get_cached_report() == NULL) {
      reportIfFalse(0, "Failed - newtest42");
    } else {
      scv_report_handler::clear_cached_report();
    }
    cout << endl;
    cout <<  "************************END TEST *******************" << endl <<  endl;
  }

  scv_report_handler::force(hold);
}

class my_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<packet_t> p;
  scv_smart_ptr<int> s;
  SCV_CONSTRAINT_CTOR(my_constraint) {
    SCV_CONSTRAINT(s() >= 1 && s() <= 100);
  }
};

/////////////////////////////////////////////////////////////
// function: test_reproducibility
//   - set_random resulting in same set of random values
/////////////////////////////////////////////////////////////
void test_reproducibility(void)
{

  scv_random* gen = new scv_random("gen", 200);
  scv_shared_ptr<scv_random> g(gen);

  scv_smart_ptr<int> sp_2;
  sp_2->set_random(g);

  cout << endl;
  cout << "Test sharing scv_random between various different smart_ptr" << endl;
  cout << "Following 25 values should always be the same for all runs" << endl;
  cout << "The values will only change when underlying value generation algorithm changes" << endl;
  {
    scv_smart_ptr<int> sp_1;

    sp_1->set_random(g);

    for (int i=0; i < 5; i++) {
      sp_1->next();
      cout << *sp_1 << endl;
    }
  }

  cout << endl;
  {
    for (int i=0; i < 5; i++) {
      sp_2->next();
      cout << *sp_2 << endl;
    }
  }


  cout << endl;
  cout << "Check reproducibility for composite data type packet_t" << endl;
  {
   scv_smart_ptr<packet_t> pp;
    scv_shared_ptr<scv_random> gen(new scv_random("gen", 200));

    pp->set_random(gen);
    for (int i = 0; i<5; ++i) {
      pp->next();
      cout << (pp->packet_type) << endl;
      cout << pp->src << endl;
      cout << pp->dest << endl;
      cout << pp->payload << endl;
      cout << endl;
    }
  }

  cout << "Check reproducibility for constraint class" << endl;
  cout << "  - First 4 elements unconstrained in the set of 5 values" << endl;
  cout << "  - Last element s >= 1 && s <= 99" << endl;
  cout << endl;
  {
    my_constraint c("c");
    scv_shared_ptr<scv_random> gen(new scv_random("gen", 200));

    c.set_random(gen);
    for (int i=0; i < 5; i++) {
      c.next();
      cout << c.p->packet_type << endl;
      cout << c.p->src << endl;
      cout << c.p->dest << endl;
      cout << c.p->payload << endl;
      cout << *c.s << endl;
    }

  }

  cout << "Check reproducibility based on use_constraint use model" << endl;
  cout << "  - Values between s >= 1 && s <= 99" << endl;
  cout << endl;
  {
    my_constraint c("c");
    scv_shared_ptr<scv_random> gen(new scv_random("gen", 200));

    scv_smart_ptr<int> my_data;

    my_data->set_random(gen);
    my_data->use_constraint(c.s);
    for (int i=0; i < 5; i++) {
      my_data->next();
      cout << *my_data << endl;
    }

  }
}

/////////////////////////////////////////////////////////////////////////
// Use constraint model for checking copying constraint objects
//   - constraint3
//   - parameterized constraint
/////////////////////////////////////////////////////////////////////////

class constraint11 : virtual public scv_constraint_base {
public:
  scv_smart_ptr<int> a;

  SCV_CONSTRAINT_CTOR(constraint11) {
    SCV_CONSTRAINT( a() >= 0 && a() <= 10);
  }

};

class constraint12 : virtual public constraint11 {
public:
  scv_smart_ptr<int> b;

  SCV_CONSTRAINT_CTOR(constraint12) {
    SCV_BASE_CONSTRAINT(constraint11);
    SCV_CONSTRAINT( b() >= 10 && b() <= 20);
  }

};

class constraint13 : public constraint12 {
public:
  scv_smart_ptr<int> c;
  scv_smart_ptr<unsigned> d;

  SCV_CONSTRAINT_CTOR(constraint13) {
    SCV_BASE_CONSTRAINT(constraint12);
    SCV_BASE_CONSTRAINT(constraint11);
    SCV_CONSTRAINT( c() >= 20 && c() <= 30);
    SCV_CONSTRAINT( d() >= 100 && d() <= 300);
  }

};


void test_copy_use_constraint_model()
{
  constraint13* c3 = new constraint13("c3");

  {
    scv_smart_ptr<int> sp;
    scv_smart_ptr<unsigned> spu;

    sp->use_constraint(c3->c);
    spu->use_constraint(c3->d);

    delete c3;

    int val_sp = *sp;
    int val_spu = *spu;

    cout << val_sp << "  " << val_spu << endl;

    reportIfFalse(val_sp >= 20 && val_sp <= 30, "Failed - newtest43");
    reportIfFalse(val_spu >= 100 && val_spu <= 300, "Failed - newtest44");


    for (int i =0; i < 5 ; i++ ) {
      sp->next();
      spu->next();

      cout << *sp << "  " << *spu << endl;
      // NEWTEST: sp[20,30] && spu[100,300]
      val_sp = *sp;
      val_spu = *spu;

      reportIfFalse(val_sp >= 20 && val_sp <= 30, "Failed - newtest45");
      reportIfFalse(val_spu >= 100 && val_spu <= 300, "Failed - newtest46");
    }
  }

  param_constraint pc("pc");

  for (int i =0 ; i < 5; i++) {
    scv_smart_ptr<int> sp;

    *pc.lb = i*10 + 10; *pc.ub = i*10 + 20;
    sp->use_constraint(pc.val);
    sp->next();
    cout << *sp << endl;
    // NEWTEST: sp[*pc.lb, *pc.ub]
    int val_lb = *pc.lb;
    int val_ub = *pc.ub;
    int val_sp = *sp;

    reportIfFalse(val_sp >= val_lb && val_sp <= val_ub, "Failed - newtest47");
  }


}

struct atm_cell_header_t {
  sc_uint<4>  gfc;
  sc_uint<8>  vpi;
  sc_uint<16> vci;
  sc_uint<4>  clp_pt;
  sc_uint<8>  hec;
};

struct atm_cell_t {
  atm_cell_header_t hdr;
};

template<>
class scv_extensions<atm_cell_header_t> : public scv_extensions_base<atm_cell_header_t> {
public:
  scv_extensions<sc_uint<4>  > gfc;
  scv_extensions<sc_uint<8>  > vpi;
  scv_extensions<sc_uint<16> > vci;
  scv_extensions<sc_uint<4>  > clp_pt;
  scv_extensions<sc_uint<8>  > hec;

  SCV_EXTENSIONS_CTOR(atm_cell_header_t) {
    SCV_FIELD(gfc);
    SCV_FIELD(vpi);
    SCV_FIELD(vci);
    SCV_FIELD(clp_pt);
    SCV_FIELD(hec);
  }
};

template<>
class scv_extensions<atm_cell_t> : public scv_extensions_base<atm_cell_t> {
public:
  scv_extensions<atm_cell_header_t > hdr;

  SCV_EXTENSIONS_CTOR(atm_cell_t) {
    SCV_FIELD(hdr);
  }
};

class atm_constraint : public scv_constraint_base {
public:
  scv_smart_ptr<atm_cell_t> cell;

  SCV_CONSTRAINT_CTOR(atm_constraint) {
    SCV_CONSTRAINT(cell->hdr.gfc() >= 1 && cell->hdr.gfc() <=2 );
    SCV_CONSTRAINT(cell->hdr.vpi() >= 1 && cell->hdr.vpi() <=2 );
    SCV_CONSTRAINT(cell->hdr.vci() >= 1 && cell->hdr.vci() <=2 );
    SCV_CONSTRAINT(cell->hdr.clp_pt() >= 1 && cell->hdr.clp_pt() <=2 );
    SCV_CONSTRAINT(cell->hdr.hec() >= 1 && cell->hdr.hec() <=2 );
  }
};

void test_nested_composite_constraint()
{

  {
    atm_constraint ac("ac");

    ac.next();

    cout << ac.cell->hdr.gfc << " " ;
    cout << ac.cell->hdr.vpi << " " ;
    cout << ac.cell->hdr.vci << " " ;
    cout << ac.cell->hdr.clp_pt << " " ;
    cout << ac.cell->hdr.hec << endl;
    cout << endl;
    // NEWTEST: Check for individual fields to satisfy constraints

    int val_gfc = ac.cell->hdr.gfc;
    int val_vpi = ac.cell->hdr.vpi;
    int val_vci = ac.cell->hdr.vci;
    int val_clp_pt = ac.cell->hdr.clp_pt;
    int val_hec = ac.cell->hdr.hec;

    reportIfFalse(val_gfc >= 1 && val_gfc <= 2, "Failed - newtest48");
    reportIfFalse(val_vpi >= 1 && val_vpi <= 2, "Failed - newtest49");
    reportIfFalse(val_vci >= 1 && val_vci <= 2, "Failed - newtest50");
    reportIfFalse(val_clp_pt >= 1 && val_clp_pt <= 2, "Failed - newtest51");
    reportIfFalse(val_hec >= 1 && val_hec <= 2, "Failed - newtest52");
  }

  {
    atm_constraint ac("ac");

    ac.set_mode(scv_extensions_if::RANDOM_AVOID_DUPLICATE);

    for (int i=0; i < 64; i++) {
      ac.next();

      cout << ac.cell->hdr.gfc << " " ;
      cout << ac.cell->hdr.vpi << " " ;
      cout << ac.cell->hdr.vci << " " ;
      cout << ac.cell->hdr.clp_pt << " " ;
      cout << ac.cell->hdr.hec << endl;

      if (i == 31) {
        cout << endl << endl;
      }
      // NEWTEST: RANDOM_AVOID_DUPLICATE (NOT_YET)
    }
  }
}


//////////////////////////////////////////////////////////
//
//
//
//////////////////////////////////////////////////////////
class constraint_sc_types : public scv_constraint_base {
public:
  scv_smart_ptr<sc_int<8> >  sp;
  scv_smart_ptr<sc_uint<64> >  sp_1;
  scv_smart_ptr<sc_uint<64> >  sp_2;

  SCV_CONSTRAINT_CTOR(constraint_sc_types) {
    SCV_CONSTRAINT( (sp() >= 5) && (sp() <= 100) );
    SCV_CONSTRAINT( sp_1() == sp_2() );
  }

};

void test_constraints_on_sc_types()
{
  constraint_sc_types c("c");

  sc_int<8> val;
  sc_uint<64> val_1;
  sc_uint<64> val_2;

  for (int i=0; i < 20; i++) {
    c.next();
    c.print();

    val = *c.sp;
    val_1 = *c.sp_1;
    val_2 = *c.sp_2;

    reportIfFalse(val >=5 && val <= 100, "Failed newtest 53");
    reportIfFalse(val_1 == val_2, "Failed newtest 54");
  }
}
