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


#ifndef ROUTER_HEADER
#define ROUTER_HEADER

//
// A router module for use with transport level components
//
// It takes REQ's from target_port and routes them to the correct
// initiator_port[p] according to the ADDRESS.
//
// It then returns the RSP to the originating target_port.
//
// It assumes :
// (i) the request must have an ADDRESS &get_address() method 
// (ii) the default constructor for the response sets the status to error
// (iii) ADDRESS has <,>, >>, and  -, operators defined.
//

#include "tlm.h"

#include "address_map.h"
#include "router_port.h"

using tlm::tlm_transport_if;

using utils::router_port;
using utils::address_map;

namespace utils
{

template< typename ADDRESS , typename REQ , typename RSP >
class router :
  public virtual tlm_transport_if< REQ , RSP > ,
  public sc_module
{
public:
  typedef  tlm_transport_if< REQ ,RSP > if_type;

  router_port< if_type > r_port;
  sc_export<if_type> target_port;

  router( sc_module_name module_name ,
	  const char *file_name = 0 ) :
    sc_module( module_name ) ,
    r_port("router_port") {

    target_port( *this );
    calculate_map_file_name( file_name );

  }

  RSP transport( const REQ &req ) {

    REQ new_req = req;
    int port_index;

    if( !amap.decode( new_req.get_address() ,
		      new_req.get_address() ,
		      port_index ) ) {

      return RSP();

    }

    return r_port[port_index]->transport( new_req );

  }

  void calculate_map_file_name( const char * );
  void end_of_elaboration();

private:
  address_map<ADDRESS> amap;
  string map_file_name;

};

template< typename ADDRESS , typename REQ , typename RSP >
void
router<ADDRESS,REQ,RSP>::
end_of_elaboration() {

  ifstream fmap( map_file_name.c_str() );

  string if_name;
  ADDRESS from , to;
  int p;

  if( fmap.is_open() ) {
    cout << "Reading " <<  map_file_name.c_str() << endl;
  }

  else {
    cout << "Cannot open file " <<  map_file_name.c_str() << endl;
    return;
  }
  
  fmap >> hex;

  while( !fmap.eof() ) {

    fmap >> if_name >> from >> to;

    if( r_port.get_port_index( if_name , p ) ) {

      cout << if_name << " : " << from << "," << to << "; " << p << endl; 
      amap.add_to_map( from , to , p );

    }
    else
      cout << "Not found " << if_name << " in port list of " << r_port.name() << endl;
 
  }

}

template< typename ADDRESS , typename REQ , typename RSP >
void
router<ADDRESS, REQ , RSP>::
calculate_map_file_name( const char *file_name  ) {

  if( file_name != 0 ) {
    cout << "Non zero file name" << endl;
    map_file_name = file_name;
  }
  else {
    cout << "Calculating file name " << endl;
    cout << name() << endl;
    const char *full_name = name();
    map_file_name = full_name;
    map_file_name = map_file_name + ".map";
  }
  
  cout << name() << " : router file name is " << map_file_name << endl;

}

};
#endif
