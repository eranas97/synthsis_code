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


#ifndef ROUTER_PORT_HEADER
#define ROUTER_PORT_HEADER

//
// router_port provides some useful functionality for routers.
//
// it builds up a 1-1 map from port name to port id. Then we can use 
// get_port_index( name , id ) to access this mapping when we're building
// up an address map.
//
// if we do parent binding, then we use the parent's name_map, not our own.
//
// Since name_map() is public, we can also print out the names of everything 
// we're connected to, by iterating through the map, which is a useful
// debugging feature whether or not we're doing routing.
//
// We do all this by overriding the binding operators.
//
// Not a proposed part of the standard, but quite useful. Probably sould be
// in utils namespace not tlm.
//
// Note : I did not generalise to sc_port< IF , N > but stuck with
// sc_port< IF , 0 >. The reason is you get into implementation difficulties,
// in the parent binding which in sc_port are solved by adding the class
// sc_port_b and doing the parent binding there. This lack of generality
// suggests that this class should be in utils not tlm. The only way round
// the problem that I can see is to put the router_port functionality directly
// into sc_port_b.
//

#include <systemc.h>
#include <map>

using std::map;
using std::string;

namespace utils
{

template < typename IF >
class router_port : public sc_port< IF , 0 >
{
public:
  typedef sc_port<IF,0> parent_type;

  using parent_type::size;
  using parent_type::name;
  
  router_port( const char * name = 0 ) :
    sc_port< IF , 0 > ( name ) ,
    name_map_ptr( &m_name_map ) {
  }

  void operator () ( sc_export<IF> &exp )
  {

    name_map()[exp.name()] = size();
    sc_port<IF,0>::operator() ( exp );

  }

  void operator () ( IF& interface_ )
  {

    sc_object *obj =  dynamic_cast<sc_object *> ( &interface_ );

    if( obj )
    {

      name_map()[obj->name()] = size();

    }

    sc_port<IF,0>::operator() ( interface_ );

  }

  // this binds router_port to an sc_port_b parent

  void operator() ( parent_type &parent ) {

    sc_port<IF,0>::operator() ( parent );

  }

  // this binds router_port to a router_port parent

  void operator() ( router_port<IF> &parent ) {

     sc_port<IF,0>::operator() ( parent );
     name_map_ptr = &(parent.m_name_map);

  }

  bool get_port_index( const string &port_name , int &p ) {

     map<string,int>::iterator i = name_map().find( port_name );

     if( i == name_map().end() ) {

       return false;

     }

     p = (*i).second;
     return true;

  }


  virtual void end_of_elaboration() {

    map<string,int>::iterator i;

    cout << "objects bound to " << name() << endl;

    for( i = name_map().begin(); i != name_map().end(); ++i )
    {

      cout << (*i).second << " : " << (*i).first << endl;

    }

  }

  map<string,int> &name_map() {

    return *name_map_ptr;

  }

private:
  map<string,int> *name_map_ptr;
  map<string,int> m_name_map;

};

};
#endif
