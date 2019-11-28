module locker(push coin opt)
input push,coin;
reg state;
reg opt;
parameter s0=0,s1=1
always(posedge clk);
 begin
  if(state==s0)
	 begin 
	  if(coin)
		 begin
		 opt<=1;
		 state<=s1;
		 end
	 else if(push)
	   begin
	   opt<=0;
		 state<=s0;
		 end
		end


  if(state==s1)
	 begin 
	  if(coin)
		 begin
		 opt<=1;
		 state<=s1;
		 end
	 else if(push)
	   begin
	   opt<=0;
		 state<=s0;
		 end
		end
 end
endmodule

