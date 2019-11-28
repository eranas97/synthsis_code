
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

class toplevel : public sc_module
{
public:
  typedef tlm_transport_channel< basic_request< ADDRESS_TYPE , DATA_TYPE > ,
                                 basic_response< DATA_TYPE > > channel_type;

  toplevel( sc_module_name module_name ) :
    sc_module( module_name ) {

    m = new master("master");
    s = new mem_slave("slave");
    a = new channel_type;

    m->initiator_port( a->target_export );
  
    s->in_port( a->get_request_export );
    s->out_port( a->put_response_export );

  }

  ~toplevel() {

    delete m;
    delete s;
    delete a;

  }

private:
  master *m;
  mem_slave *s;
  channel_type *a;

};

#ifndef MTI_SYSTEMC
int sc_main( int argc , char **argv )
{

  toplevel top("top");

  sc_start( -1 );

  cout << "Finished" << endl;
  return 0;

}
#else
SC_MODULE_EXPORT(toplevel);
#endif
