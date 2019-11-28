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


#include "transactor.h"

using basic_protocol::READ;
using basic_protocol::WRITE;
using basic_protocol::SUCCESS;
using basic_protocol::ERROR;


ostream &operator<<( ostream &os , const REQUEST_TYPE &req ) {

  if( req.type == READ ) {
    os << "Read request " << req.a;
  }
  else {
    os << "Write request " << req.a << " " << req.d;
  }
  return os;

}

ostream &operator<<( ostream &os , const RESPONSE_TYPE &rsp ) {

  if( rsp.type == READ ) {
    os << "Read response " << rsp.d;
  }
  else {
    os << "Write response ";
  }

  if( rsp.status == ERROR ) {
    os << ": ERROR";
  }

  return os;

}

transactor::transactor( sc_module_name module_name ) :
  sc_module( module_name ) ,
  clk("clk") , 
  rst("rst") ,
  enable("en") , 
  rw("rw") ,
  ack("ack") ,
  err("err" ) ,
  address("address") ,
  wr_data("wr_data" ) ,
  rd_data("rd_data" ) {

  SC_METHOD( run );
  sensitive << clk.pos();
  dont_initialize();

}

void transactor::run() {

  if( rst ) {

    m_state = EXECUTE;
    got_request = false;
    put_status = true;

    enable = false;
    
  }

  else {

    switch( m_state ) {

    case EXECUTE :

      if( ack == true ) {

	m_state = WAIT;
	enable = false;
	got_request = false;

	if( err ) {
	  rsp.status = ERROR;
	}
	else {
	  rsp.status = SUCCESS;
	}

	if( rw ) {
	  rsp.type = READ;
	  rsp.d = rd_data.read();
	}
	else {
	  rsp.type = WRITE;
	}

	cout << name() << " " << sc_time_stamp();
	cout << " got response " << rsp << endl;

	put_status = response_port->nb_put( rsp );
	
	if( !put_status ) {

	  cout << name() << " " << sc_time_stamp();
	  cout << "no room in fifo for " << rsp << endl;

	}

      }

      else {

	if( !got_request ) {

	  got_request = request_port->nb_get( req );
	  
	}

	if( got_request ) {

	  enable = true;
	
	  address = req.a;
	  if( req.type == WRITE ) {
	    rw = false;
	    wr_data = req.d;
	  }
	  else {
	    rw = true;
	  }
	
	  cout << name() << " " << sc_time_stamp();
	  cout << " sending request " << req << endl;

	}

      }

      break;

    case WAIT :

      enable = false;

      if( !put_status ) {
	put_status = response_port->nb_put( rsp );
      }

      if( put_status ) {
	m_state = EXECUTE;
      }
      
      break;

    default :
      cout << name() << " Unknown state" << endl;
      break;
    }

  }

}
