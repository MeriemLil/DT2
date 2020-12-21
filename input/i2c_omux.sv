`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_omux
  
  (
   input logic 	clk,
   input logic 	rst_n,
   input logic 	oe_in,
   input logic 	osel_in,
   input logic 	ack_in,
   input logic 	sd_in,
   output logic sdaw_out
   );

   logic 	sdaw;

   always_comb
     begin
	if (osel_in == 0)
	 sdaw = ack_in;
	else
	 sdaw = sd_in;
     end

   always_comb 
     begin
	case ({oe_in, sdaw})
	  2'b00: sdaw_out = 'z;
	  2'b01: sdaw_out = 'z;
	  2'b10: sdaw_out = 0;
 	  2'b11: sdaw_out = 'z;
	  default: sdaw_out = 0;
	 endcase
     end
   
   
endmodule


