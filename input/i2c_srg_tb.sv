`ifndef SYNTHESIS

`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_srg_tb #(parameter DUT_VS_REF_SIMULATION = 0);

   logic clk;
   logic rst_n;
   logic clr_in;
   logic next_in;
   logic bit_in;
   logic bit_out;
   logic addrok_out;

   // DUT instantiation   
   i2c_srg DUT_INSTANCE (.*);

  // TEST program instantiation   
   i2c_srg_test TEST (.*);

    // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   // REF model instantiation

   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic ref_bit_out;
	 logic ref_addrok_out;	 
	 i2c_srg REF_INSTANCE(.bit_out(ref_bit_out),
			      .addrok_out(ref_addrok_out),			      
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
