
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


#include "pipelined_master.h"

using pipelined_protocol::READ;
using pipelined_protocol::WRITE;
using pipelined_protocol::ADDRESS_OK;

using pipelined_protocol::address_phase_request;
using pipelined_protocol::address_phase_status;
using pipelined_protocol::data_phase_request;
using pipelined_protocol::data_phase_response;

pipelined_master::pipelined_master( sc_module_name module_name ) :
  sc_module( module_name ) ,
  outstanding( "outstanding" , -16 ) {

  SC_THREAD( address_phase );
  SC_THREAD( data_phase );

}

void pipelined_master::address_phase() {

  for( int i = 0; i < 20; i++ ) {

    initiate_write( i , i + 50 );
    initiate_read( i );

  }

}

bool pipelined_master::initiate_write( const ADDRESS_TYPE &a ,
				       const DATA_TYPE &d ) {

  address_phase_request<ADDRESS_TYPE> address_req;
  data_phase_request<DATA_TYPE> data_req;

  address_req.type = data_req.type = WRITE;
  
  address_req.a = a;
  data_req.wr_data = d;

  cout << name() << " sending " << address_req << endl;

  if( address_port->transport( address_req ) != ADDRESS_OK ) {
    return false;
  }
   
  outstanding.put( data_req );
  return true;
}

bool pipelined_master::initiate_read( const ADDRESS_TYPE &a ) {

  address_phase_request<ADDRESS_TYPE> address_req;
  data_phase_request<DATA_TYPE> data_req;

  address_req.type = data_req.type = READ;
  
  address_req.a = a;

  cout << name() << " sending " << address_req << endl;

  if( address_port->transport( address_req ) != ADDRESS_OK ) {
    return false;
  }
   
  outstanding.put( data_req );
  return true;

}

void pipelined_master::data_phase() {

  data_phase_request<ADDRESS_TYPE> data_req;
  data_phase_response<DATA_TYPE> data_rsp;

  while( true ) {

    data_req = outstanding.get();

    cout << name() << " sending " << data_req << endl;

    data_rsp = data_port->transport( data_req );

    cout << name() << " recieved " << data_rsp << endl << endl;

  }

}



