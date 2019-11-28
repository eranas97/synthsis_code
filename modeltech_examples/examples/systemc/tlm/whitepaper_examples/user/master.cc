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

using user::master;

master::master( sc_module_name module_name ) :
  sc_module( module_name ) , 
  initiator_port("iport")
{
  SC_THREAD( run );
}

void master::run()
{

  DATA_TYPE d;

  for( ADDRESS_TYPE a = 0; a < 20; a++ )
  {

    cout << "Writing Address " << a << " value " << a + 50 << endl;
    initiator_port.write( a , a + 50 );

  }

  for( ADDRESS_TYPE a = 0; a < 20; a++ )
  {

    initiator_port.read( a , d );
    cout << "Read Address " << a << " got " << d << endl;

  }
}
