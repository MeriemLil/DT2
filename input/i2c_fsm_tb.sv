`include "myfilter.svh"
import myfilter_pkg::*;

`ifndef SYNTHESIS

module i2c_fsm_tb  #(parameter DUT_VS_REF_SIMULATION = 0);
   
   logic clk;
   logic rst_n;
   logic start_in;
   logic stop_in;
   logic scl_rise_in;
   logic scl_fall_in;
   logic addrok_in;
   logic byteok_in;
   logic frameok_in;
   logic lastbit_in;
   logic ul_out;
   logic dl_out;
   logic byteen_out;   
   logic sde_out; 
   logic clr_out; 
   logic next_out;
   logic ack_out;
   logic oe_out;
   logic osel_out;
   
   
   // DUT instantiation

   i2c_fsm DUT_INSTANCE (.*);


  // TEST program instantiation   
   i2c_fsm_test TEST (.*);

    // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   // REF model instantiation

   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic ref_sde_out;
	 logic ref_ul_out;
	 logic ref_oe_out;
	 logic ref_osel_out;
	 logic ref_next_out;
	 logic ref_clr_out; 	 
	 
	 i2c_fsm REF_INSTANCE
	   (.sde_out(ref_sde_out),
	    .ul_out(ref_ul_out),
	    .oe_out(ref_oe_out),
	    .osel_out(ref_osel_out),	    
	    .clr_out(ref_clr_out),
	    .next_out(ref_next_out)	    
	    );
      end 
   endgenerate
   
   // Clock generator process

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
