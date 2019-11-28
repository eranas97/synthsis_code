
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

#ifndef TRANSACTOR_HEADER
#define TRANSACTOR_HEADER

#include <systemc.h>

#include "bus_types.h"
#include "tlm.h"

using tlm::tlm_nonblocking_get_if;
using tlm::tlm_nonblocking_put_if;

class transactor :
  public sc_module
{
public:

  transactor( sc_module_name module_name );

  sc_port< tlm_nonblocking_get_if< REQUEST_TYPE > > request_port;
  sc_port< tlm_nonblocking_put_if< RESPONSE_TYPE > > response_port;

  SC_HAS_PROCESS( transactor );

  sc_in<bool> clk;
  sc_in<bool> rst;

  sc_out<bool>           enable;
  sc_out< bool >         rw;
  sc_in<bool>            ack;
  sc_in<bool>            err;
 
  sc_out< sc_uint< ADDRESS_WIDTH> > address;
  sc_out< sc_uint< DATA_WIDTH > >   wr_data;
  sc_in< sc_uint< DATA_WIDTH > >   rd_data;

private:
  
  enum state {

    EXECUTE ,
    WAIT
    
  };

  void run();

  REQUEST_TYPE req;
  RESPONSE_TYPE rsp;

  bool got_request;
  bool put_status;

  sc_signal< state > m_state;

};

#endif
