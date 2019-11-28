
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


#include "mem_fifo_slave.h"

using basic_protocol::basic_request;
using basic_protocol::basic_response;

mem_slave::mem_slave( sc_module_name module_name , int k ) :
  sc_module( module_name ) ,
  in_port("in_port") , out_port("out_port")
{

  SC_THREAD( run );
  memory = new ADDRESS_TYPE[k * 1024];

}

void mem_slave::run()
{

  basic_request<ADDRESS_TYPE,DATA_TYPE> request;
  basic_response<DATA_TYPE> response;
 
  for(;;)
  {

    request = in_port->get();

    response.type = request.type;

    switch( request.type )
    {
    case basic_protocol::READ :

      response.d = memory[request.a];
      response.status = basic_protocol::SUCCESS;

      break;

    case basic_protocol::WRITE:

      memory[request.a] = request.d;
      response.status = basic_protocol::SUCCESS;

      break;

    default:

      response.status = basic_protocol::SUCCESS;
      break;

    }

    out_port->put( response );

  }

}

mem_slave::~mem_slave()
{

  delete [] memory;

}
