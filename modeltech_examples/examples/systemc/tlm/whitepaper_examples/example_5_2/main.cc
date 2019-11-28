
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


#include "switch_master.h"
#include "mem_slave.h"
#include "simple_arb.h"
#include "router.h"

using tlm::tlm_transport_if;
using tlm::tlm_transport_channel;

using basic_protocol::basic_request;
using basic_protocol::basic_response;

using utils::router;
using utils::simple_arb;

using user::switch_master;
using user::mem_slave;

typedef tlm_transport_channel< basic_request< ADDRESS_TYPE , DATA_TYPE > ,
			     basic_response< DATA_TYPE > > arb_channel_type;

typedef simple_arb< basic_request< ADDRESS_TYPE , DATA_TYPE > ,
		    basic_response< DATA_TYPE > > arb_type;

typedef router< ADDRESS_TYPE ,
		basic_request< ADDRESS_TYPE , DATA_TYPE > ,
		basic_response< DATA_TYPE > > router_type;

class top : public sc_module
{
public:
  top( sc_module_name nm ) :
    sc_module( nm ) ,
    m0("master_0" , 0 , 57 ) ,
    m1("master_1" , 1 , 1000 ) ,
    m0_to_s0("m0s0") ,
    m0_to_s1("m0s1") ,
    m1_to_s0("m1s0") , 
    m1_to_s1("m1s1") ,
    arb0("arb0") ,
    arb1("arb1") ,
#ifdef MTI_SYSTEMC
    router0("router0" , "router0.map" ) ,
    router1("router1" , "router1.map" ) ,
#else
    router0("router0" , "router0-osci.map" ) ,
    router1("router1" , "router1-osci.map" ) ,
#endif /* MTI_SYSTEMC */
    s0("slave_0") ,
    s1("slave_1")
  {
  
    // connectivity pattern is master -> router -> channel -> arbiter -> slave

    m0.initiator_port( router0.target_port ); // master 0 to router 0
    m1.initiator_port( router1.target_port ); // master 1 to router 1

    router0.r_port( m0_to_s0.target_export );
    router0.r_port( m0_to_s1.target_export );
    router1.r_port( m1_to_s0.target_export );
    router1.r_port( m1_to_s1.target_export );

    arb0.master_port[0]( m0_to_s0.slave_export ); 
    arb0.master_port[1]( m1_to_s0.slave_export );
    arb1.master_port[0]( m0_to_s1.slave_export );
    arb1.master_port[1]( m1_to_s1.slave_export );

    arb0.slave_port( s0.target_port );
    arb1.slave_port( s1.target_port );

    // set arbitration priorities ( can be done from file if needed )

    arb0.add_interface( &arb0.master_port[0] , 3 ); 
    arb0.add_interface( &arb0.master_port[1] , 2 );

    arb1.add_interface( &arb1.master_port[0] , 3 ); 
    arb1.add_interface( &arb1.master_port[1] , 2 );
     
  }

private:   
  
  switch_master m0, m1;

  arb_channel_type m0_to_s0 , m0_to_s1;
  arb_channel_type m1_to_s0 , m1_to_s1;

  arb_type arb0 , arb1;

  router_type router0 , router1;

  mem_slave s0 , s1;
   
};

#ifndef MTI_SYSTEMC
int sc_main( int argc , char **argv )
{

  top t("top");
 
  sc_start( 100 , SC_NS );

  return 0;

}
#else
SC_MODULE_EXPORT( top );
#endif
