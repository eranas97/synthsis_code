
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


#include "pipelined_slave.h"

using pipelined_protocol::ADDRESS_OK;
using pipelined_protocol::ADDRESS_ERROR;
using pipelined_protocol::DATA_OK;
using pipelined_protocol::DATA_ERROR;
using pipelined_protocol::READ;
using pipelined_protocol::WRITE;

pipelined_slave::pipelined_slave( sc_module_name module_name ,
				  int k , int d ) :
  sc_module( module_name ) {

  address_export( *this );
  data_export( *this );
  
  memory = new DATA_TYPE[k * 1024];
  pipeline = new tlm_fifo< address_phase_request< ADDRESS_TYPE > >( d ); 

}

pipelined_slave::~pipelined_slave() {

  delete [] memory;

  if( pipeline->nb_can_get() ) {

    cout << "Warning : requests not processed in slave" << endl;

  }

  delete pipeline;

}

address_phase_status
pipelined_slave::
transport( const address_phase_request< ADDRESS_TYPE > &req ) {

  // could do range checking as well

  if( req.type != READ && req.type != WRITE ) {
    return address_phase_status( ADDRESS_ERROR );
  }

  pipeline->put( req );
  cout << name() << req << " entering pipeline " << endl;

  return address_phase_status( ADDRESS_OK );
}

data_phase_response<DATA_TYPE>
pipelined_slave::
transport( const data_phase_request< DATA_TYPE > &req ) {

  data_phase_response<DATA_TYPE > rsp;
  address_phase_request< ADDRESS_TYPE > pending;

  while( pipeline->nb_can_put() ) {
    wait( pipeline->ok_to_get() );
  }

  cout << name() << req << " leaving pipeline " << endl;

  pipeline->nb_peek( pending );

  if( pending.type != req.type ) {
    rsp.status = DATA_ERROR;
    return rsp;
  }

  pipeline->get();

  rsp.status = DATA_OK; // assumes range checking done in address phase
  rsp.type = req.type;

  switch( req.type ) {
  case READ :
    rsp.rd_data = memory[pending.a];
    break;
  case WRITE :
    memory[pending.a] = req.wr_data;
    break;
  default :
    assert( 0 ); // default already checked on way in to fifo
  }

  return rsp;

}

