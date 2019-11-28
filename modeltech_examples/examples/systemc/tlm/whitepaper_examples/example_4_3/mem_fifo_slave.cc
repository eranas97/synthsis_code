
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

mem_slave::mem_slave( sc_module_name module_name , int r ) :
  sc_module( module_name ) ,
  request_port("in_port") , response_port("out_port") ,
  remainder( r )
{

  SC_THREAD( run );
  memory = new ADDRESS_TYPE[1024];

}

void mem_slave::run()
{

  basic_request<ADDRESS_TYPE,DATA_TYPE> req;

  while( true ) {

    request_port->peek( req );

    if( decode( req.a ) ) {

      basic_response<DATA_TYPE> rsp;
    
      request_port->get();
      rsp = process_request( req );
      response_port->put( rsp );

    }

    wait( request_port->ok_to_get() );

  }

}

bool mem_slave::decode( const ADDRESS_TYPE &a )
{

  return static_cast<int>(a % 2) == remainder; 

} 

basic_response< DATA_TYPE >
mem_slave::
process_request( const basic_request< ADDRESS_TYPE , DATA_TYPE > &request )
{

  basic_response<DATA_TYPE> response;
  ADDRESS_TYPE a = request.a >> 1;

  response.type = request.type;

  switch( request.type ) {
  case basic_protocol::READ :

    response.d = memory[a];
    response.status = basic_protocol::SUCCESS;

    cout << name() << " read " << response.d << " from " << a << endl;

    break;

  case basic_protocol::WRITE:

    memory[a] = request.d;
    response.status = basic_protocol::SUCCESS;

    cout << name() << " written " << request.d << " to " << a << endl;
    break;

  default:

    response.status = basic_protocol::ERROR;
    break;
    
  }
  
  return response;

}

mem_slave::~mem_slave()
{

  delete [] memory;

}
