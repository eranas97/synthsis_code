// Macro for fix-point type 
#define SC_INCLUDE_FX    

// Macro for registering a class member function
#define MTI_BIND_SC_MEMBER_FUNCTION     

#include "systemc.h"
#include "sc_dpiheader.h"
#include <iostream>

SC_MODULE(scdpi_types_top)
{     
   void call_verilog_task(); //top level SC_THREAD

   //SystemVerilog DPI import functions that will be registered in the constructor

   void sc_fix_func(sc_fix param1, sc_fix param2, sc_fix *func_out);
   void sc_fix_fast_func(sc_fix_fast param1, sc_fix_fast param2,sc_fix_fast *func_out);
   void sc_ufix_func(sc_ufix param1, sc_ufix param2,sc_ufix *func_out);
   void sc_ufix_fast_func(sc_ufix_fast param1, sc_ufix_fast param2,sc_ufix_fast *func_out);
   void sc_fixed_func(sc_fixed<6,4> param1, sc_fixed<6,4> param2,sc_fixed<6,4> *func_out);
   void sc_fixed_fast_func(sc_fixed_fast<6,4> param1, sc_fixed_fast<6,4> param2,sc_fixed_fast<6,4> *func_out);
   void sc_ufixed_func(sc_ufixed<6,4> param1, sc_ufixed<6,4> param2,sc_ufixed<6,4> *func_out);
   void sc_ufixed_fast_func(sc_ufixed_fast<6,4> param1, sc_ufixed_fast<6,4> param2,sc_ufixed_fast<6,4> *func_out);
   void sc_signed_func(sc_signed param1, sc_signed param2, sc_signed *func_out);
   void sc_unsigned_func(sc_unsigned param1, sc_unsigned param2, sc_unsigned *func_out);
   void sc_int_func(sc_int<8> param1, sc_int<8> param2, sc_int<8> *func_out);
   void sc_uint_func(sc_uint<8> param1, sc_uint<8> param2,sc_uint<8> *func_out);
   void sc_bigint_func(sc_bigint<40> param1, sc_bigint<40> param2,sc_bigint<40> *func_out);
   void sc_biguint_func(sc_biguint<40> param1, sc_biguint<40> param2, sc_biguint<40> *func_out);
   void sc_bit_func(sc_bit param1, sc_bit param2, sc_bit *func_out);
   void sc_bv_func(sc_bv<4> param1, sc_bv<4> param2,sc_bv<4> *func_out);
   void sc_logic_func(sc_logic param1, sc_logic param2,sc_logic *func_out);
   void sc_lv_func(sc_lv<4> param1, sc_lv<4> param2, sc_lv<4> *func_out);


   //SystemVerilog DPI export tasks called from SC_THREAD.

   void call_sc_fix_task();             // for type sc_fix
   void call_sc_ufix_task();            // for type sc_ufix
   void call_sc_fix_fast_task();        // for type sc_fix_fast
   void call_sc_ufix_fast_task();       // for type sc_ufix_fast
   void call_sc_fixed_task();           // for type sc_fixed
   void call_sc_fixed_fast_task();      // for type sc_fixed_fast
   void call_sc_ufixed_task();          // for type sc_ufixed
   void call_sc_ufixed_fast_task();     // for type sc_ufixed_fast
   void call_sc_signed_task();          // for sc_signed type
   void call_sc_unsigned_task();        // for sc_unsigned type
   void call_sc_int_task();             // for sc_int type
   void call_sc_uint_task();            // for sc_uint type
   void call_sc_bigint_task();          // for sc_bigint type
   void call_sc_biguint_task();         // for sc_biguint type
   void call_sc_bit_task();             // for sc_bit type
   void call_sc_bv_task();              // for sc_bv type
   void call_sc_logic_task();           // for sc_logic type
   void call_sc_lv_task();              // for sc_lv type

   SC_CTOR(scdpi_types_top)
   {
       SC_THREAD(call_verilog_task);     
       set_stack_size(1000000);         //set stack to be 10M


#ifdef MTI_BIND_SC_MEMBER_FUNCTION

       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_fix_func", &scdpi_types_top::sc_fix_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_ufix_func", &scdpi_types_top::sc_ufix_func); 
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_fix_fast_func", &scdpi_types_top::sc_fix_fast_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_ufix_fast_func", &scdpi_types_top::sc_ufix_fast_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_fixed_func", &scdpi_types_top::sc_fixed_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_fixed_fast_func", &scdpi_types_top::sc_fixed_fast_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_ufixed_func", &scdpi_types_top::sc_ufixed_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_ufixed_fast_func", &scdpi_types_top::sc_ufixed_fast_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_signed_func", &scdpi_types_top::sc_signed_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_unsigned_func", &scdpi_types_top::sc_unsigned_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_int_func", &scdpi_types_top::sc_int_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_uint_func", &scdpi_types_top::sc_uint_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_bigint_func", &scdpi_types_top::sc_bigint_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_biguint_func", &scdpi_types_top::sc_biguint_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_bit_func", &scdpi_types_top::sc_bit_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_bv_func", &scdpi_types_top::sc_bv_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_logic_func", &scdpi_types_top::sc_logic_func);  
       SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_lv_func", &scdpi_types_top::sc_lv_func);  
#endif
      
   }

   ~scdpi_types_top() {};
};


void scdpi_types_top::call_verilog_task()
{   
    svSetScope(svGetScopeFromName("top"));
    call_sc_fix_task();
    wait(1, SC_NS);
    call_sc_fix_fast_task();
    wait(1, SC_NS);
    call_sc_ufix_task();
    wait(1, SC_NS);
    call_sc_ufix_fast_task();
    wait(1, SC_NS);
    call_sc_fixed_task();
    wait(1, SC_NS);
    call_sc_fixed_fast_task();
    wait(1, SC_NS);
    call_sc_ufixed_task();
    wait(1, SC_NS);
    call_sc_ufixed_fast_task();
    wait(1, SC_NS);
    call_sc_signed_task();
    wait(1, SC_NS);
    call_sc_unsigned_task();
    wait(1, SC_NS);
    call_sc_int_task();
    wait(1, SC_NS);
    call_sc_uint_task();
    wait(1, SC_NS);
    call_sc_bigint_task();
    wait(1, SC_NS);
    call_sc_biguint_task();
    wait(1, SC_NS);
    call_sc_bit_task();
    wait(1, SC_NS);
    call_sc_bv_task();
    wait(1, SC_NS);
    call_sc_logic_task();
    wait(1, SC_NS);
    call_sc_lv_task();
    wait(1, SC_NS);
}


//****************************  sc_fix TYPE **************************************
     
void scdpi_types_top::sc_fix_func(sc_fix param1, sc_fix param2 , sc_fix *func_out) 
{   
    cout << "******************  sc_fix TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_fix_func param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_fix_func param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_fix_func param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_fix_task()
{
    sc_fix op1(6,4);
    sc_fix op2(6,4);
    sc_fix task_out(8,6);
    sc_fix task_out1(12,8);
    sc_fix div_out(6,4);
    sc_fix div_op1(12,8);
    
    div_op1= 4.75;

    op1= -3.75;
    op2 =-1.25;

     
    cout << "******************  sc_fix TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

     
    for (int op_index = 0; op_index < 11; op_index++)
    {        
        if (op_index < 6) {
            sc_fix_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }        
        else if ((op_index > 5) && (op_index < 8)) {
            sc_fix_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out << endl;
        }
        else if (op_index == 8) {
            sc_fix_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out1 << endl;
        }
        else if (op_index == 9) {   
            sc_fix_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << div_out << endl;
        }
        else if (op_index == 10) {
            sc_fix_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
    }     
}


//****************************  sc_fix_fast TYPE **************************************
     
void scdpi_types_top::sc_fix_fast_func(sc_fix_fast param1, sc_fix_fast param2,sc_fix_fast *func_out) 
{   
    cout << "******************  sc_fix_fast TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_fix_fast_func param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_fix_fast_func param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_fix_fast_func param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_fix_fast_task()
{
    sc_fix_fast op1(6,4);
    sc_fix_fast op2(6,4);
    sc_fix_fast task_out(8,6);
    sc_fix_fast task_out1(12,8);
    sc_fix_fast div_out(6,4);
    sc_fix_fast div_op1(12,8);

    div_op1= 4.75;

    op1= -3.75;
    op2 =-2.25;
     
    cout << "******************  sc_fix_fast TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++)
    {        
        if (op_index < 6) {
            sc_fix_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }        
        else if ((op_index > 5) && (op_index < 8)) {
            sc_fix_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out << endl;
        }        
        else if (op_index == 8) {
            sc_fix_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out1 << endl;
        }
        else if (op_index == 9) {   
            sc_fix_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << div_out << endl;
        }
        else if (op_index == 10) {
            sc_fix_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
    }     
}

//****************************  sc_ufix TYPE **************************************
void scdpi_types_top::sc_ufix_func(sc_ufix param1, sc_ufix param2,sc_ufix *func_out) 
{   
    cout << "******************  sc_ufix TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_ufix_func param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_ufix_func param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_ufix_func param1 ^ param2 = " << *func_out << endl;
   
}

void scdpi_types_top::call_sc_ufix_task()
{
    sc_ufix op1(6,4);
    sc_ufix op2(6,4);
    sc_ufix task_out(8,6);
    sc_ufix task_out1(12,8);
    sc_ufix div_out(6,4);
    sc_ufix div_op1(12,8);

    div_op1= 4.75;
    op1= 3.75;
    op2 =2.25;

    cout << "******************  sc_ufix TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++)
    {
        if ( op_index < 6) {
            sc_ufix_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
        
        else if ((op_index > 5) && (op_index < 8)) {   
            sc_ufix_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out << endl;
        }
        
        else if (op_index == 8) {
            sc_ufix_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out1 << endl;
        }
        else if (op_index == 9) {   
            sc_ufix_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << div_out << endl;
        }

        else if (op_index == 10) {
            sc_ufix_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
    }
}

//****************************  sc_ufix_fast TYPE **************************************
void scdpi_types_top::sc_ufix_fast_func(sc_ufix_fast param1, sc_ufix_fast param2,sc_ufix_fast *func_out) 
{
    cout << "******************  sc_ufix_fast TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_ufix_func param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_ufix_func param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_ufix_func param1 ^ param2 = " << *func_out << endl;   
}

void scdpi_types_top::call_sc_ufix_fast_task() 
{
    sc_ufix_fast op1(6,4);
    sc_ufix_fast op2(6,4);
    sc_ufix_fast task_out(8,6);
    sc_ufix_fast task_out1(12,8);
    sc_ufix_fast div_out(6,4);
    sc_ufix_fast div_op1(12,8);

    div_op1= 4.75;
    op1= 3.75;
    op2 =2.25;

    cout << "******************  sc_ufix_fast TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if ( op_index < 6) {
            sc_ufix_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
        else if ((op_index > 5) && (op_index < 8)) {   
            sc_ufix_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out << endl;
        }
        else if (op_index == 8) {
            sc_ufix_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out1 << endl;
        }
        else if (op_index == 9) {   
            sc_ufix_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << div_out << endl;
        }
        else if (op_index == 10) {
            sc_ufix_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
    }
}

//****************************  sc_fixed TYPE **************************************

void scdpi_types_top::sc_fixed_func(sc_fixed<6,4> param1, sc_fixed<6,4> param2,sc_fixed<6,4> *func_out) 
{
    cout << "******************  sc_fixed TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_fixed param1 | param2 = " <<*func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_fixed param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_fixed param1 ^ param2 = " << *func_out << endl;   
}

void scdpi_types_top::call_sc_fixed_task() 
{
    sc_fixed<6,4>  op1;
    sc_fixed<6,4>  op2;
    sc_fixed<8,6>  task_out;
    sc_fixed<12,8> task_out1;
    sc_fixed<6,4>  div_out;
    sc_fixed<12,8> div_op1;

    div_op1= 4.75;
    op1= 3.75;
    op2 =-1.75;

    cout << "******************  sc_fixed TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if ( op_index < 6) {
            sc_fixed_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
        else if ((op_index > 5) && (op_index < 8)) {   
            sc_fixed_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out << endl;
        }
        else if (op_index == 8) {
            sc_fixed_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out1 << endl;
        }
        else if (op_index == 9) {   
            sc_fixed_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << div_out << endl;
        }
        else if (op_index == 10) {
            sc_fixed_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
    }
}

//****************************  sc_fixed_fast TYPE **************************************

void scdpi_types_top::sc_fixed_fast_func(sc_fixed_fast<6,4> param1, sc_fixed_fast<6,4> param2,sc_fixed_fast<6,4> *func_out) 
{
    cout << "******************  sc_fixed_fast TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_fixed param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_fixed param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_fixed param1 ^ param2 = " << *func_out << endl;   
}

void scdpi_types_top::call_sc_fixed_fast_task() 
{
    sc_fixed_fast<6,4>  op1;
    sc_fixed_fast<6,4>  op2;
    sc_fixed_fast<8,6>  task_out;
    sc_fixed_fast<12,8> task_out1;
    sc_fixed_fast<6,4>  div_out;
    sc_fixed_fast<12,8> div_op1;

    div_op1= 4.75;
    op1= 3.5;
    op2 =-1.25;

    cout << "******************  sc_fixed_fast TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if ( op_index < 6) {
            sc_fixed_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
        else if ((op_index > 5) && (op_index < 8)) {   
            sc_fixed_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out << endl;
        }
        else if (op_index == 8) {
            sc_fixed_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out1 << endl;
        }
        else if (op_index == 9) {   
            sc_fixed_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << div_out << endl;
        }
        else if (op_index == 10) {
            sc_fixed_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
    }
}

//****************************  sc_ufixed TYPE **************************************

void scdpi_types_top::sc_ufixed_func(sc_ufixed<6,4> param1, sc_ufixed<6,4> param2,sc_ufixed<6,4> *func_out) 
{
    cout << "******************  sc_ufixed TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_ufixed param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_ufixed param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_ufixed param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_ufixed_task() 
{
    sc_ufixed<6,4>  op1;
    sc_ufixed<6,4>  op2;
    sc_ufixed<8,6>  task_out;
    sc_ufixed<12,8> task_out1;
    sc_ufixed<6,4>  div_out;
    sc_ufixed<12,8> div_op1;
    
    div_op1= 4.75;
    op1= 5.75;
    op2 =3.75;

    cout << "******************  sc_ufixed TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if ( op_index < 6) {
            sc_ufixed_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
        else if ((op_index > 5) && (op_index < 8)) {   
            sc_ufixed_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out << endl;
        }
        else if (op_index == 8) {
            sc_ufixed_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out1 << endl;
        }
        else if (op_index == 9) {   
            sc_ufixed_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << div_out << endl;
        }
        else if (op_index == 10) {
            sc_ufixed_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
    }
}

//****************************  sc_ufixed_fast TYPE **************************************

void scdpi_types_top::sc_ufixed_fast_func(sc_ufixed_fast<6,4> param1, sc_ufixed_fast<6,4> param2,sc_ufixed_fast<6,4>* func_out) 
{
    cout << "******************  sc_ufixed_fast TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_fixed param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_fixed param1 & param2 = " <<* func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_fixed param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_ufixed_fast_task() 
{
    sc_ufixed_fast<6,4>  op1;
    sc_ufixed_fast<6,4>  op2;
    sc_ufixed_fast<8,6>  task_out;
    sc_ufixed_fast<12,8> task_out1;
    sc_ufixed_fast<6,4>  div_out;
    sc_ufixed_fast<12,8> div_op1;

    div_op1= 4.75;
    op1= 7.25;
    op2 =2.5;

    cout << "******************  sc_ufixed_fast TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;
    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if ( op_index < 6) {
            sc_ufixed_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
        
        else if ((op_index > 5) && (op_index < 8)) {   
            sc_ufixed_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out << endl;
        }
        else if (op_index == 8) {
            sc_ufixed_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << task_out1 << endl;
        }
        else if (op_index == 9) {   
            sc_ufixed_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
            cout << div_out << endl;
        }

        else if (op_index == 10) {
            sc_ufixed_fast_task(op1, op2, op_index, &task_out, &task_out1, div_op1, &div_out);
        }
    }
}


//****************************  sc_signed TYPE **************************************
     
void scdpi_types_top::sc_signed_func(sc_signed param1, sc_signed param2, sc_signed *func_out) 
{
    cout << "******************  sc_signed TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_signed param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_signed param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_signed param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_signed_task() 
{
    sc_signed op1(8);
    sc_signed op2(8);
    sc_signed task_out(8);
    sc_signed task_out1(8);
    
    op1= -20;
    op2 =-5;
     
    cout << "******************  sc_signed TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;
    
    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if (op_index < 6) {
            sc_signed_task(op1, op2, op_index, &task_out, &task_out1);
        }
        
        else if ((op_index > 5) && (op_index < 8)) {
            sc_signed_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out << endl;
        }
        else if ((op_index == 8) || (op_index == 9)) {
            sc_signed_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out1 << endl;
        }
        else if (op_index == 10) {
            sc_signed_task(op1, op2, op_index, &task_out, &task_out1);
        }
    }
}

//****************************  sc_unsigned TYPE **************************************
     
void scdpi_types_top::sc_unsigned_func(sc_unsigned param1, sc_unsigned param2,sc_unsigned *func_out) 
{
    cout << "******************  sc_unsigned TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_unsigned param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_unsigned param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_unsigned param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_unsigned_task() 
{
    sc_unsigned op1(8);
    sc_unsigned op2(8);
    sc_unsigned task_out(8);
    sc_unsigned task_out1(8);
    
    op1= 16;
    op2 =8;
     
    cout << "******************  sc_unsigned TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;
    
    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if (op_index < 6) {
            sc_unsigned_task(op1, op2, op_index, &task_out, &task_out1);
        }
        
        else if ((op_index > 5) && (op_index < 8)) {
            sc_unsigned_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out << endl;
        }
        else if ((op_index == 8) || (op_index == 9)) {
            sc_unsigned_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out1 << endl;
        }
        else if (op_index == 10) {
            sc_unsigned_task(op1, op2, op_index, &task_out, &task_out1);
        }
    }     
}


//****************************  sc_int TYPE **************************************
     
void scdpi_types_top::sc_int_func(sc_int<8> param1, sc_int<8> param2 ,sc_int<8> *func_out) 
{
    cout << "******************  sc_int TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_int param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_int param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_int param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_int_task() 
{
    sc_int<8> op1;
    sc_int<8> op2;
    sc_int<8> task_out;
    sc_int<8> task_out1;

    op1= -15;
    op2 =-5;
     
    cout << "******************  sc_int TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;
    
    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if (op_index < 6) {
            sc_int_task(op1, op2, op_index, &task_out, &task_out1);
        }
        else if ((op_index > 5) && (op_index < 8)) {
            sc_int_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out << endl;
        }
        else if ((op_index == 8) || (op_index == 9)) {
            sc_int_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out1 << endl;
        }
        else if (op_index == 10) {
            sc_int_task(op1, op2, op_index, &task_out, &task_out1);
        }
    }     
}

//****************************  sc_uint TYPE **************************************
     
void scdpi_types_top::sc_uint_func(sc_uint<8> param1, sc_uint<8> param2, sc_uint<8> *func_out) {
    cout << "******************  sc_uint TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_unsigned param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_unsigned param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_unsigned param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_uint_task() 
{
    sc_uint<8> op1;
    sc_uint<8> op2;
    sc_uint<8> task_out;
    sc_uint<8> task_out1;

    op1= 12;
    op2 =4;
     
    cout << "******************  sc_unsigned TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if (op_index < 6) {
            sc_uint_task(op1, op2, op_index, &task_out, &task_out1);
        }
        else if ((op_index > 5) && (op_index < 8)) {
            sc_uint_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out << endl;
        }
        else if ((op_index == 8) || (op_index == 9)) {
            sc_uint_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out1 << endl;
        }
        else if (op_index == 10) {
            sc_uint_task(op1, op2, op_index, &task_out, &task_out1);
        }
    }     
}

//****************************  sc_bigint TYPE **************************************
     
void scdpi_types_top::sc_bigint_func(sc_bigint<40> param1, sc_bigint<40> param2, sc_bigint<40> *func_out) 
{
    cout << "******************  sc_bigint TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_bigint param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_bigint param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_bigint param1 ^ param2 = " << *func_out << endl;
}       

void scdpi_types_top::call_sc_bigint_task() 
{
    sc_bigint<40> op1;
    sc_bigint<40> op2;
    sc_bigint<128> task_out;
    sc_bigint<128> task_out1;

    op1= -101665525214LL;
    op2 =-170385001950LL;
     
    cout << "******************  sc_bigint TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if (op_index < 6) {
            sc_bigint_task(op1, op2, op_index, &task_out, &task_out1);
        }
        else if ((op_index > 5) && (op_index < 8)) {
            sc_bigint_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out << endl;
        }
        else if ((op_index == 8) || (op_index == 9)) {
            sc_bigint_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out1 << endl;
        }
        else if (op_index == 10) {
            sc_bigint_task(op1, op2, op_index, &task_out, &task_out1);
        }
    }
}
//****************************  sc_biguint TYPE **************************************
     
void scdpi_types_top::sc_biguint_func(sc_biguint<40> param1, sc_biguint<40> param2, sc_biguint<40> *func_out) 
{
    cout << "******************  sc_biguint TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_unsigned param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_unsigned param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_unsigned param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_biguint_task() 
{
    sc_biguint<40>  op1;
    sc_biguint<40>  op2;
    sc_biguint<128> task_out;
    sc_biguint<128> task_out1;

    op1 = 15766179294LL; //3AB BC CD DE
    op2 = 11471211998LL; //2AB BC CD DE
     
    cout << "******************  sc_biguint TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {        
        if (op_index < 6) {
            sc_biguint_task(op1, op2, op_index, &task_out, &task_out1);
        }
        else if ((op_index > 5) && (op_index < 8)) {
            sc_biguint_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out << endl;
        }
        else if ((op_index == 8) || (op_index == 9)) {
            sc_biguint_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out1 << endl;
        }
        else if (op_index == 10) {
            sc_biguint_task(op1, op2, op_index, &task_out, &task_out1);
        }
    }
}

//****************************  sc_bit TYPE **************************************
     
void scdpi_types_top::sc_bit_func(sc_bit param1, sc_bit param2, sc_bit *func_out) 
{
   cout << "******************  sc_bit TYPE ********************** "<< endl;
   cout << "param1 = "<< param1 << endl;
   cout << "param2 = "<< param2 << endl;
   
   cout << "from sc func_out -----------------> = " << *func_out << endl;
   *func_out =  param1 | param2;

   cout << "from sc func_out -----------------> = " << *func_out << endl;
   cout << "from sc_bit param1 | param2 = " << *func_out << endl;
   
   *func_out = param1 & param2;
   cout << "from sc_bit param1 & param2 = " << *func_out << endl;

   *func_out = param1 ^ param2;
   cout << "from sc_bit param1 ^ param2 = " << *func_out << endl;
   
}

void scdpi_types_top::call_sc_bit_task() 
{
    sc_bit op1;
    sc_bit op2;
    sc_bit task_out;
    sc_bit task_out1;

    op1= '1';
    op2 ='1';
     
    cout << "******************  sc_bit TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if (op_index < 6) {
            sc_bit_task(op1, op2, op_index, &task_out, &task_out1);
        }        
        else if ((op_index > 5) && (op_index < 8)) {
            sc_bit_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out << endl;
        }
        else if ((op_index == 8) || (op_index == 9)) {
            sc_bit_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out1 << endl;
        }
        else if (op_index == 10) {
            sc_bit_task(op1, op2, op_index, &task_out, &task_out1);
        }
    }
}
//****************************  sc_bv TYPE **************************************
     
void scdpi_types_top::sc_bv_func(sc_bv<4> param1, sc_bv<4> param2, sc_bv<4> *func_out) 
{
    cout << "******************  sc_bv TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_unsigned param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_unsigned param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_unsigned param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_bv_task() 
{
    sc_bv<4> op1;
    sc_bv<4> op2;
    sc_bv<8> task_out;
    sc_bv<8> task_out1;

    op1= "1100";  
    op2 ="0100";  
     
    cout << "******************  sc_bv TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {
        if (op_index < 6) {
            sc_bv_task(op1, op2, op_index, &task_out, &task_out1);
        }        
        else if ((op_index > 5) && (op_index < 8)) {
            sc_bv_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out << endl;
        }
        else if ((op_index == 8) || (op_index == 9)) {
            sc_bv_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out1 << endl;
        }
        else if (op_index == 10) {
            sc_bv_task(op1, op2, op_index, &task_out, &task_out1);
        }
    }     
}

//****************************  sc_logic TYPE **************************************
     
void scdpi_types_top::sc_logic_func(sc_logic param1, sc_logic param2 , sc_logic *func_out) 
{   
    cout << "******************  sc_logic TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_logic param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_logic param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_logic param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_logic_task() 
{
    sc_logic op1;
    sc_logic op2;
    sc_logic task_out;
    sc_logic task_out1;

    op1= '1';
    op2 ='1';
     
    cout << "******************  sc_logic TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {        
        if (op_index < 6) {
            sc_logic_task(op1, op2, op_index, &task_out, &task_out1);
        }
        else if ((op_index > 5) && (op_index < 8)) {
            sc_logic_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out << endl;
        }
        else if ((op_index == 8) || (op_index == 9)) {
            sc_logic_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out1 << endl;
        }
        else if (op_index == 10) {
            sc_logic_task(op1, op2, op_index, &task_out, &task_out1);
        }
    }     
}
//****************************  sc_lv TYPE **************************************
     
void scdpi_types_top::sc_lv_func(sc_lv<4> param1, sc_lv<4> param2, sc_lv<4> *func_out) 
{   
    cout << "******************  sc_lv TYPE ********************** "<< endl;
    cout << "param1 = "<< param1 << endl;
    cout << "param2 = "<< param2 << endl;
   
    *func_out = param1 | param2;
    cout << "from sc_unsigned param1 | param2 = " << *func_out << endl;
   
    *func_out = param1 & param2;
    cout << "from sc_unsigned param1 & param2 = " << *func_out << endl;

    *func_out = param1 ^ param2;
    cout << "from sc_unsigned param1 ^ param2 = " << *func_out << endl;
}

void scdpi_types_top::call_sc_lv_task() 
{
    sc_lv<4> op1;
    sc_lv<4> op2;
    sc_lv<8> task_out;
    sc_lv<8> task_out1;

    op1= "1100";  
    op2 ="0100";  
     
    cout << "******************  sc_lv TYPE ********************** "<< endl;
    cout << "op1 value = "<< op1 << endl;
    cout << "op2 value = "<< op2 << endl;

    for (int op_index = 0; op_index < 11; op_index++) 
    {        
        if (op_index < 6) {
            sc_lv_task(op1, op2, op_index, &task_out, &task_out1);
        }        
        else if ((op_index > 5) && (op_index < 8)) {
            sc_lv_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out << endl;
        }
        else if ((op_index == 8) || (op_index == 9)) {
            sc_lv_task(op1, op2, op_index, &task_out, &task_out1);
            cout << task_out1 << endl;
        }
        else if (op_index == 10) {
            sc_lv_task(op1, op2, op_index, &task_out, &task_out1);
        }
    }
}

SC_MODULE_EXPORT(scdpi_types_top);
