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


#include "my_master.h"

my_master::my_master( sc_module_name module_name ) :
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

void my_master::run() {

  if( rst ) {

    m_address = 0;
    m_wr_data = 50;

    m_state = RESET;    
    enable = false;
    
  }

  else {

    switch( m_state ) {
    case RESET :
      enable = false;
      m_state = WRITE;
      break;
    case WRITE :

      if( ack == true ) {

	m_state = WRITE_WAIT;
	enable = false;

	if( err ) {

	  cout << name() << " " << sc_time_stamp();
	  cout << " error on write " << m_address << " , " << m_wr_data << endl;

	}

      }

      else {

	enable = true;
	rw = false;
	address = m_address;
	wr_data = m_wr_data;

	cout << name() << " " << sc_time_stamp();
	cout << " writing " << m_address << " , " << m_wr_data << endl;

      }

      break;

    case WRITE_WAIT :

      enable = false;
      m_wr_data = m_wr_data.read() + 1;
      m_state = READ;
      break;

    case READ :
      
     if( ack == true ) {

	m_state = READ_WAIT;
	enable = false;

	if( err ) {

	  cout << name() << " " << sc_time_stamp();
	  cout << " error on read " << m_address << endl;

	}
	else {
	  
	  cout << name() << " " << sc_time_stamp();
	  cout << " read " << m_address << " , " << rd_data << endl;

	}

      }

      else {

	enable = true;
	rw = true;
	address = m_address;

	cout << name() << " " << sc_time_stamp();
	cout << " reading " << m_address << endl;

      }

      break;

    case READ_WAIT :

      enable = false;
      m_address = m_address.read() + 1;
      m_state = WRITE;
      break;

    default :
      cout << name() << " Unknown state" << endl;
      break;
    }

  }

}
