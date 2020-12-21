`ifndef SYNTHESIS

`include "myfilter.svh"
import myfilter_pkg::*;
import i2c_pkg::*;

module i2c_sync_tb #(parameter DUT_VS_REF_SIMULATION = 0);

   logic clk;
   logic rst_n;
   logic sda_in;   
   logic scl_in;
   logic sda_out;
   logic scl_out;
   logic past_sda_out;
   logic past_scl_out;
   
   i2c_sync DUT_INSTANCE (.*);


  // TEST program instantiation   
   i2c_sync_test TEST (.*);

    // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   // REF model instantiation

   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic ref_sda_out;
	 logic ref_scl_out;
	 logic ref_past_sda_out;
	 logic ref_past_scl_out;
	 i2c_sync REF_INSTANCE(.sda_out(ref_sda_out),
			       .scl_out(ref_scl_out),
			       .past_sda_out(ref_past_sda_out),
			       .past_scl_out(ref_past_scl_out),
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
