
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
#include "mem_fifo_slave.h"

using tlm::tlm_transport_channel;
using basic_protocol::basic_request;
using basic_protocol::basic_response;

using user::master;

typedef tlm_transport_channel< basic_request< ADDRESS_TYPE , DATA_TYPE > ,
		             basic_response< DATA_TYPE > > channel_type;


class top : public sc_module
{
public:
  top( sc_module_name nm ) :
    sc_module( nm ) , 
    m("master" ) ,
    s0("even_slave" , 0 ) , 
    s1("odd_slave" , 1 ) 
  {

    m.initiator_port( a.target_export );

    s0.request_port( a.get_request_export );
    s0.response_port( a.put_response_export );
    
    s1.request_port( a.get_request_export );
    s1.response_port( a.put_response_export );
 
  }

private:   
 
  master        m;
  mem_slave     s0;
  mem_slave     s1;
  channel_type  a;
  
};

#ifndef MTI_SYSTEMC
int sc_main( int argc , char **argv )
{

  top t("top");

  sc_start( -1 );
  return 0;

}
#else
SC_MODULE_EXPORT( top );
#endif

