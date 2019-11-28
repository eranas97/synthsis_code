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


#ifndef MY_MASTER_HEADER
#define MY_MASTER_HEADER

#include <systemc.h>

class my_master : public sc_module
{
public:

  my_master( sc_module_name module_name );

  SC_HAS_PROCESS( my_master );

  sc_in<bool> clk;
  sc_in<bool> rst;

  sc_out<bool>           enable;
  sc_out< sc_uint<8> >   address;
  sc_out< bool >         rw;
  sc_out< sc_uint< 8 > > wr_data;
  sc_in< sc_uint< 8 > >  rd_data;
  sc_in<bool>            ack;
  sc_in<bool>            err;
  
private:
  enum state {

    RESET ,
    WRITE ,
    WRITE_WAIT , 
    READ ,
    READ_WAIT

  };

  void run();

  sc_signal< sc_uint< 8 > > m_address;
  sc_signal< sc_uint< 8 > > m_wr_data;
  sc_signal< state > m_state;

};

#endif
