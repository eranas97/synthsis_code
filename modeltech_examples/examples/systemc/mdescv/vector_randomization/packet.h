// nbcode "packet" start
struct frame_t {
  sc_uint<32> dest_addr;
  sc_uint<32> src_addr;
  sc_uint<24> tag;
  sc_uint<8>  type;
  sc_uint<64> data;
  sc_uint<32> crc;
};

struct packet_t {
  frame_t      frame;
  sc_uint<16> msg_length;
  char        msg[16];
};
// nbcode "packet" end

// nbcode "out" start
//define an ostream for a packet object
ostream& operator<<(ostream& os, const packet_t& p) {
  os << "{\n"
     << "   src_addr: " << p.frame.src_addr << "\n"
     << "   dest_addr: " << p.frame.dest_addr << "\n"
     << "   msg_length: " << p.msg_length << "\n"
     << "   msg {\n     ";

  for (int i = 0; i < 16; i++)
     os << p.msg[i];

  os << "\n"
     << "   }\n}" << endl;
  return os;
}
// nbcode "out" end

