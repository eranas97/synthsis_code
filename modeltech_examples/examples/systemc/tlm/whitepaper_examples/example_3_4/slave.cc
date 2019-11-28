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


#include "slave.h"

slave::slave( sc_module_name module_name ) : 
  sc_module( module_name ) ,
  clk("clk") , 
  rst("rst") ,
  enable("en") , 
  address("address") ,
  rw("rw") ,
  wr_data("wr_data" ) ,
  rd_data("rd_data" ) ,
  ack("ack") ,
  err("err" ) {

  SC_METHOD( run );
  sensitive << clk.pos();
  dont_initialize();

}

void slave::run() {

  if( rst ) {

    m_state = RESET;
    ack = false;

  }

  else {
    
    switch( m_state ) {
    case RESET :
      ack = false;
      m_state = READY;
      m_count = ready_count;
      break;
    case READY :
      if( enable ) {
	m_count = m_count - 1;

	if( m_count == 0 ) {

	  ack = true;
	  m_state = RESET;
	  
	  cout << name() << " " << sc_time_stamp();

	  if( address.read() >= memory_size ) {
	    err = true;
	    cout << " error " << endl;
	  }

	  else {

	    err = false;

	    if( rw ) {
	      
	      cout << " reading " << memory[address.read()] << " from " << address << endl;
	      rd_data = memory[address.read()];

	    }

	    else {
	      
	      cout << " writing " << wr_data << " to " << address << endl;
	      memory[address.read()] = wr_data.read();
	      
	    }

	  }

	}

	else {
	  ack = false;
	  cout << name() << " " << sc_time_stamp();
	  cout << " no ack " << address << " " << m_count << endl;
	}

      }

      else {
	ack = false;
      }

      break;
    default :
      cout << name() << " Unknown state" << endl;
      break;

    }

  }

}
