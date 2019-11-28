
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


#include "master.h"
#include "simple_arb.h"
#include "mem_slave.h"

using tlm::tlm_transport_channel;

using basic_protocol::basic_request;
using basic_protocol::basic_response;

using utils::simple_arb;

using user::master;
using user::mem_slave;

class toplevel : public sc_module
{
public:
  typedef tlm_transport_channel< basic_request< ADDRESS_TYPE , DATA_TYPE > ,
		                 basic_response< DATA_TYPE > > arb_channel_type;

  toplevel( sc_module_name module_name ) :
    sc_module( module_name ) ,
    m1("master1") , 
    m2("master2") ,
    arb("arb") ,
    s("slave") {

    m1.initiator_port( c1.target_export );
    m2.initiator_port( c2.target_export );

    arb.master_port[0]( c1.slave_export ); // ie m1 -> c1 -> master_port[0]
    arb.master_port[1]( c2.slave_export ); // ie m2 -> c2 -> master_port[1]

    arb.slave_port( s.target_port );

    arb.add_interface( &arb.master_port[0] , 3 );
    arb.add_interface( &arb.master_port[1] , 2 );


  }

private:
  master m1 , m2;
  simple_arb< basic_request< ADDRESS_TYPE , DATA_TYPE > ,
	      basic_response< DATA_TYPE > >  arb;
  mem_slave s;
  arb_channel_type c1 , c2;

};

#ifndef MTI_SYSTEMC
int sc_main( int argc , char **argv )
{
 
  toplevel *top = new toplevel("top");

  sc_start( 100 , SC_NS );

  cout << "Finished" << endl;
  delete top;

  return 0;

}

#else

SC_MODULE_EXPORT( toplevel );

#endif
