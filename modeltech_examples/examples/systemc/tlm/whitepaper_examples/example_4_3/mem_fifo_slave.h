
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

#ifndef MEM_SLAVE_HEADER
#define MEM_SLAVE_HEADER

#include "systemc.h"

#include "bus_types.h"
#include "basic_protocol.h"
#include "basic_slave_base.h"

using tlm::tlm_get_peek_if;
using tlm::tlm_blocking_put_if;

using basic_protocol::basic_request;
using basic_protocol::basic_response;

class mem_slave :
  public sc_module
{
public:
  mem_slave( sc_module_name module_name , int r );

  SC_HAS_PROCESS( mem_slave );
  
  sc_port<
    tlm_get_peek_if <
      basic_request< ADDRESS_TYPE , DATA_TYPE >
    >
  > request_port;
  
  sc_port<
    tlm_blocking_put_if <
      basic_response< DATA_TYPE >
    >
  > response_port;

  ~mem_slave();

private:
  void run();

  bool decode( const ADDRESS_TYPE &a );
  
  basic_response< DATA_TYPE >
  process_request( const basic_request< ADDRESS_TYPE , DATA_TYPE > &req );

  ADDRESS_TYPE *memory;
  int remainder;

};

#endif
