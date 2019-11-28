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


/*
 * Address / Data Phase Pipelined protocol
 */

#ifndef PIPELINED_PROTOCOL_HEADER
#define PIPELINED_PROTOCOL_HEADER

#include "tlm.h"

using tlm::tlm_transport_if;

namespace pipelined_protocol {

enum pipelined_protocol_type {

  READ , 
  WRITE

};

//
// this is the response type for the address phase
//

enum address_phase_status { 

  ADDRESS_OK ,
  ADDRESS_ERROR

};

enum data_phase_status {

  DATA_OK , 
  DATA_ERROR

};

template < typename ADDRESS > 
struct address_phase_request {

  pipelined_protocol_type type;
  ADDRESS a;

};

template < typename DATA > 
struct data_phase_request {

  pipelined_protocol_type type;
  DATA wr_data;

};

template < typename DATA >
struct data_phase_response {

  pipelined_protocol_type type;
  DATA rd_data;
  data_phase_status status;

};


template< typename ADDRESS >
ostream &operator<<( ostream &os ,
		     const address_phase_request< ADDRESS > &req ) {
 switch( req.type ) {
  case READ :
    os << "(Address Phase) Read Request ";
    break;

  case WRITE :
    os << "(Address Phase) Write Request ";
    break;

  default :
    os << "(Address Phase) Unknown Request ";
    break;

  }

  os << req.a;
  return os;

}

template< typename DATA >
ostream &operator<<( ostream &os ,
		     const data_phase_request< DATA > &req ) {
 switch( req.type ) {
  case READ :
    os << "(Data Phase) Read Request ";
    break;

  case WRITE :
    os << "(Data Phase) Write Request " << req.wr_data;
    break;

  default :
    os << "(Data Phase) Unknown Request ";
    break;

  }

  return os;

}

template< typename DATA >
ostream &operator<<( ostream &os ,
		     const data_phase_response< DATA > &rsp ) {

  if( rsp.status != DATA_OK ) {

    os << "(Data Phase) Read Response Error ";
    return os;

  }

  switch( rsp.type ) {
  case READ :
    os << "(Data Phase) Read Response " << rsp.rd_data;
    break;

  case WRITE :
    os << "(Data Phase Protocol) Write Response ";
    break;
    
  default :
    os << "(Data Phase Protocol) Unknown Response ";
    break;
    
  }

  return os;

}

};
#endif
