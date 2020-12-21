`include "myfilter.svh"
import myfilter_pkg::*;

program i2c_omux_test
  
  (
   input logic 	clk,
   input logic 	rst_n,
   output logic oe_in,
   output logic osel_in,
   output logic ack_in,
   output logic sd_in,
   input logic 	sdaw_out
   );

   initial
     begin : test_program
	$info("T1: RANDOM");
	
	for ( int bits = 0; bits <= 15; ++bits)
	  begin
	     { oe_in, osel_in, ack_in, sd_in } = bits;
	     @(negedge clk);
	  end
	
	@(negedge clk);

	$finish;
	
     end : test_program
   
   
endprogram


