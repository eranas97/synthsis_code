
/*****************************************************************************

  The following code is derived, directly or indirectly, from the SystemC
  source code Copyright (c) 1996-2004 by all Contributors.
  All Rights reserved.

  The contents of this file are subject to the restrictions and limitations
  set forth in the SystemC Open Source License Version 2.4 (the "License");
  You may not use this file except in compliance with such restrictions and
  limitations. You may obtain instructions on how to receive a copy of the
  License at http://www.systemc.org/. Software distributed by Contributors
  under the License is distributed on an "AS IS" basis, WITHOUT WARRANTY OF
  ANY KIND, either express or implied. See the License for the specific
  language governing rights and limitations under the License.

 *****************************************************************************/

#ifndef SLAVE_HEADER
#define SLAVE_HEADER

#include <systemc.h>

const int ready_count = 1;
const int memory_size = 16;

class slave : public sc_module
{
public:

  slave( sc_module_name module_name );

  SC_HAS_PROCESS( slave );

  sc_in<bool> clk;
  sc_in<bool> rst;

  sc_in<bool>             enable;
  sc_in< sc_uint< 8 > >   address;
  sc_in<bool>             rw;
  sc_in< sc_uint < 8 > >  wr_data;
  sc_out< sc_uint < 8 > > rd_data;
  sc_out<bool>            ack;
  sc_out<bool>            err;


private:


  enum state {
    RESET ,
    READY
  };

  state m_state;
  sc_signal<int> m_count;
  void run();

  sc_uint<8> memory[memory_size];

};

#endif
