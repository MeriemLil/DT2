`ifndef SYNTHESIS
`include "myfilter.svh"
import myfilter_pkg::*;

module filter_unit_tb  #(parameter DUT_VS_REF_SIMULATION = 0);
   
   // Testbench signals
   logic clk;
   logic rst_n;
   logic sde_in;
   logic sd_in;
   logic sd_out;
   logic ul_in;
   logic dl_in;   
   logic [DATABITS-1:0]        ext_in;
   logic 		       extready_in;
   logic [DATABITS-1:0]        ext_out;
   logic 		      extvalid_out;
   
   // DUT module instantiation
   filter_unit DUT_INSTANCE (.*);

  // TEST program instantiation   
   filter_unit_test TEST (.*);

   // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic 		      ref_sd_out;
	 logic [DATABITS-1:0] ref_ext_out;
	 logic 		      ref_extvalid_out;
	 filter_unit REF_INSTANCE(.ext_out(ref_ext_out),
				  .extvalid_out(ref_extvalid_out),
				  .sd_out(ref_sd_out),
				  .*);
      end 
   endgenerate

   // Clock generator
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
