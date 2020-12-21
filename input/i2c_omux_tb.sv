`ifndef SYNTHESIS

`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_omux_tb #(parameter DUT_VS_REF_SIMULATION = 0);

   logic clk;
   logic rst_n;
   logic oe_in;
   logic osel_in;
   logic ack_in;
   logic sd_in;
   logic sdaw_out;

   // DUT instantiation      
   i2c_omux DUT_INSTANCE (.*);


  // TEST program instantiation   
   i2c_omux_test TEST (.*);

   // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   // REF model instantiation

   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic ref_sdaw_out;
	 i2c_omux3 REF_INSTANCE(.sdaw_out(ref_sdaw_out),
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
