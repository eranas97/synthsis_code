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

using user::switch_master;

switch_master::switch_master( sc_module_name module_name ,
			      bool p ,
			      DATA_TYPE s , 
			      ADDRESS_TYPE m ) :
  sc_module( module_name ) , 
  initiator_port("iport") ,
  parity( p ) , 
  start_data( s ) ,
  max_address( m )
{
  SC_THREAD( run );
}

void switch_master::run()
{

  DATA_TYPE d;

  for( ADDRESS_TYPE a = start_address();
       a < start_address() + max_address;
       a += 2 )
  {

    cout << name() << " Writing Address " << a % max_address;
    cout << " value " << a + start_data << endl;
 
    initiator_port.write( a % max_address , a + start_data );

  }

  for( ADDRESS_TYPE a = start_address();
       a < start_address() + max_address;
       a += 2 )
  {

    initiator_port.read( a % max_address , d );

    cout << name() << " Read Address " << a % max_address;
    cout << " got " << d << endl;

  }

  cout << name() << " Finished at " << sc_time_stamp() << endl;

}

ADDRESS_TYPE switch_master::start_address() {

  if( !parity ) {
    return 0; // even from zero
  }
  else {
    return 1 + max_address / 2; // odd from middle ( and then round )
  }

}
