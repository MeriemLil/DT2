`ifndef SYNTHESIS
`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_detector_tb  #(parameter DUT_VS_REF_SIMULATION = 0); 
   logic clk;
   logic rst_n;
   logic sda_in;
   logic scl_in;
   logic past_scl_in;
   logic past_sda_in;
   logic start_out;
   logic stop_out;
   logic scl_rise_out;
   logic scl_fall_out;
   
   i2c_detector DUT_INSTANCE (.*);

  // TEST program instantiation   
   i2c_detector_test TEST (.*);

    // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic ref_start_out;
	 logic ref_stop_out;
	 logic ref_scl_rise_out;
	 logic ref_scl_fall_out;
	 i2c_sync REF_INSTANCE(.start_out(ref_start_out),
			       .stop_out(ref_stop_out),
			       .scl_rise_out(ref_scl_rise_out),
			       .scl_fall_out(ref_scl_fall_out),
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

