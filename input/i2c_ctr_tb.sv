`ifndef SYNTHESIS

`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_ctr_tb #(parameter DUT_VS_REF_SIMULATION = 0);

   logic clk;
   logic rst_n;
   logic clr_in;
   logic next_in;
   logic byteen_in;   
   logic byteok_out;
   logic frameok_out;   

   // DUT module instantiation      
   i2c_ctr DUT_INSTANCE (.*);

  // TEST program instantiation   
   i2c_ctr_test TEST (.*);

    // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   // REF model instantiation

   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic ref_byteok_out;
	 logic ref_frameok_out;	 
	 i2c_ctr3 REF_INSTANCE(.byteok_out(ref_byteok_out),
			       .frameok_out(ref_frameok_out),
			       .*);
      end 
   endgenerate

   always
     begin
	if (clk == '0)
	  clk = '1;
	else
	  clk = '0;
	#(CLK_PERIOD/2);
     end

   // Reset generator
   initial
     begin : reset_gen
	rst_n = '0;
	@(negedge clk);
	rst_n = '1;
     end : reset_gen
   
endmodule


`endif
