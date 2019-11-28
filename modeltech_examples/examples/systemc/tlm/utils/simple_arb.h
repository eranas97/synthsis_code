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


#ifndef SIMPLE_ARB_HEADER
#define SIMPLE_ARB_HEADER

//
// arbitration is done using a many to one multimap
//
// The key to the multimap is the priority. With each key we may in general
// have many sc_port<> * data elements.
//
// virtual get_next_request scans thru the masters, getting the highest 
// port with a request pending.
//
// virtual run() calls get_next_request and forwards the request to the slave 
// and passes the response back to the appropriate master.
//
// I used a < int , sc_port<> * > mapping because I can imagine other arbiters 
// with explicitly named ports rather than an array as implemented here eg
//
// port_type high_priority_port;
// port_type low_priority_port;
// port_type debug_port;
//
// This has the downside that we have to specify the number of master ports
//

#include <map>

using std::multimap;
using std::pair;

#include "tlm.h"

using tlm::tlm_transport_if;
using tlm::tlm_slave_if;

namespace utils
{

template < typename REQ , typename RSP , int N = 2>
class simple_arb : public sc_module
{
public:
  typedef sc_port< tlm_slave_if< REQ , RSP > , 1 > port_type;

  port_type master_port[N];

  sc_port< tlm_transport_if< REQ , RSP > , 1 > slave_port;

  SC_HAS_PROCESS( simple_arb );

  simple_arb( sc_module_name module_name ,
	      const sc_time &t = sc_time( 1 , SC_NS ) ) :
    sc_module( module_name ) ,
    slave_port("slave_port") ,
    arb_t( t ) {

    SC_THREAD( run );

  }

  void add_interface( port_type *port , const int priority ) {

    if_map.insert( typename multimap_type::value_type( priority , port ) );

  }

protected:
  typedef multimap< int , port_type * > multimap_type;
  multimap_type if_map;
  sc_time arb_t;

  virtual void run() {

    port_type *port_ptr;
    typename multimap_type::iterator i;
    REQ req;
    RSP rsp;

    for( ;; ) {

      if( port_ptr = get_next_request( i , req ) ) {

	rsp = slave_port->transport( req );
	(*port_ptr)->put( rsp );

      }

      wait( arb_t );

    }

  }

  virtual port_type *get_next_request( typename multimap_type::iterator &i ,
				       REQ &req ) {


    //
    // this starvation inducing algorithm always starts from the highest priority
    // you may want to do something else in a subclass
    //

    port_type *p;

    for( i = if_map.begin(); i != if_map.end(); ++i ) {

      p = (*i).second;

      if( (*p)->nb_get( req )  ) {

	cout << name() << " " << sc_time_stamp() << " found pending request on port " << p->name() << " priority " << (*i).first << endl;
	return p;

      }

      else
	cout << name() << " " << sc_time_stamp() << " no pending request on port " << p->name() << " priority " << (*i).first << endl;

    }
  
    return 0;
  }


};

};
#endif
