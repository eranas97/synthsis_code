#include "systemc.h"
#include "sc_dpiheader.h"
#include <string>

SC_MODULE(hello_sc_top)
{
    void call_verilog_task();
    int sc_task();

    SC_CTOR(hello_sc_top)
    {
        SC_THREAD(call_verilog_task);

        SC_DPI_REGISTER_CPP_MEMBER_FUNCTION("sc_task", &hello_sc_top::sc_task);
    }

    ~hello_sc_top() {};
};

int hello_sc_top::sc_task()
{
    std::string timeStr = sc_time_stamp().to_string();

    sc_core::wait(20, SC_NS);

    printf("#\t%s hello from sc_task(). \n", timeStr.c_str());

    sc_core::wait(40, SC_NS);

    timeStr = sc_time_stamp().to_string();

    printf("#\t%s hello from sc_task(). \n", timeStr.c_str());

   return 0;
}

void hello_sc_top::call_verilog_task()
{ 
    svSetScope(svGetScopeFromName("hello_top"));

    for(int i = 0; i < 3; ++i)
    {
        verilog_task();
    }
}

SC_MODULE_EXPORT(hello_sc_top);
