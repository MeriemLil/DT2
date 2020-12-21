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
   
   
endmodule


