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


#include "bus_types.h"
#include "master.h"
#include "transactor.h"
#include "slave.h"
#include "reset.h"

using user::master;
using tlm::tlm_transport_channel;

class top : public sc_module 
{
public:   
   top( sc_module_name n ) :
   sc_module( n ) ,
     clk( "clock" , sc_time( 10 , SC_NS ) ) ,
     r("reset" , 5 ) ,
     m("master") ,
     t("transactor") , 
     s("slave")
   {
   
	 m.initiator_port( channel.target_export );
	 t.request_port( channel.get_request_export );
	 t.response_port( channel.put_response_export );


     t.clk( clk );
     t.rst( rst );
     t.enable( enable );
     t.rw( rw );
     t.ack( ack );
     t.err( err );
     t.address( address );
     t.wr_data( wr_data );
     t.rd_data( rd_data );
     
     s.clk( clk );
     s.rst( rst );
     s.enable( enable );
     s.rw( rw );
     s.ack( ack );
     s.err( err );
     s.address( address );
     s.wr_data( wr_data );
     s.rd_data( rd_data );
     
     r.clk( clk );
     r.rst( rst );
  
   }
   
private:
  sc_clock clk;
  reset r;

  master m;
  tlm_transport_channel< REQUEST_TYPE , RESPONSE_TYPE > channel;
  transactor t;
  slave s;

  sc_signal<bool>           rst;

  sc_signal<bool>           enable;
  sc_signal<bool>           rw;
  sc_signal<bool>           ack;
  sc_signal< bool >         err;
  sc_signal< sc_uint< 8 > > address;
  sc_signal< sc_uint< 8 > > wr_data;
  sc_signal< sc_uint< 8 > > rd_data;


};

#ifndef MTI_SYSTEMC
int sc_main( int argc , char **argv ) {

    top t("top");
    sc_start( 2000 , SC_NS );

}
#else
SC_MODULE_EXPORT( top );
#endif
