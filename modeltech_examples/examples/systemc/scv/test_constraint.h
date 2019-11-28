// Copyright 1991-2016 Mentor Graphics Corporation

// All Rights Reserved.

// THIS WORK CONTAINS TRADE SECRET AND PROPRIETARY INFORMATION
// WHICH IS THE PROPERTY OF MENTOR GRAPHICS CORPORATION
// OR ITS LICENSORS AND IS SUBJECT TO LICENSE TERMS.

#ifndef INCLUDED_TEST_CONSTRAINT
#define INCLUDED_TEST_CONSTRAINT

#include "systemc.h"
#include "scv/scv.h"

// Definitions for routines providing various different checks
void test_basic_class_next(void);
void test_constraint_smart_ptr();
void test_change_constraint_at_run_time();
void test_use_constraint();
void test_copy_use_constraint_model();
void test_partial_constraint_initialization();
void test_no_constraint();
void test_distribution_constriant();
void test_avoid_duplicate();
void test_value_generation_mode();
void test_disable_randomization();
void test_composite_constraint();
void test_nested_composite_constraint();
void test_over_constrained_objects();
void test_reproducibility(void);
void test_constraints_on_sc_types();
static bool success = true;
static int globalTestFailures = 0;


SC_MODULE(sctop) {
virtual void start_of_simulation()
{
  // tb_startup();
#if defined(OSCI) || defined(SCHDL) || defined(NCSC)
  scv_random::set_global_seed(scv_random::pick_random_seed());
#endif
  {
    cout << "TEST SIMPLE CONSTRAINT USE MODEL ON SIMPLE INTEGER TYPE" << endl;
    test_basic_class_next();
    test_constraint_smart_ptr();
    test_use_constraint();
    test_copy_use_constraint_model();
    test_partial_constraint_initialization();
    test_no_constraint();
    test_distribution_constriant();
    test_value_generation_mode();
    test_disable_randomization();
  }

  {
    cout << endl << endl;
    cout << "TEST COMPLEX CONSTRAINT USE MODEL" << endl;
    cout << "  -COMPOSITE DATA TYPE" << endl;
    cout << "  -INHERITANCE BASED CONSTRAINTS " << endl;

    test_composite_constraint();
    test_nested_composite_constraint();
  }

  {
    cout << endl << endl;
    cout << "TEST OVER CONSTRAINTED OBJECTS" << endl;
    test_over_constrained_objects();
  }

  {
    cout << endl << endl;
    cout << "TEST REPRODUCIBILITY" << endl;
    test_reproducibility();
  }

  {
    cout << endl << endl;
    cout << "TEST SystemC Types" << endl;
    test_constraints_on_sc_types();
  }

  cout << ( success ? TBS_SUCCESS : TBS_FAIL ) << endl;
  cout << TBS_INFO << "Exiting tb_constraints" << endl;
}
  SC_CTOR(sctop);
};

#endif
