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
#include "slave.h"
#include "reset.h"

class top : public sc_module
{
public:
  top( sc_module_name nm ) : 
    sc_module( nm ) ,
    clk( "clock" , sc_time( 10 , SC_NS ) ) ,
    r("reset" , 5  ) ,
    m("my_master") ,
    s("slave" )
  {
    m.clk( clk );
    m.rst( rst );
    m.enable( enable );
    m.rw( rw );
    m.ack( ack );
    m.err( err );
    m.address( address );
    m.wr_data( wr_data );
    m.rd_data( rd_data );
    
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
  reset r;

  my_master m;
  slave s;

  sc_clock                  clk;
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

  return 0;

}
#else
SC_MODULE_EXPORT( top );
#endif
