`ifndef SYNTHESIS
`include "myfilter.svh"
import myfilter_pkg::*;

module dpc_tb #(parameter DUT_VS_REF_SIMULATION = 0);

   logic clk;
   logic rst_n;
   logic ul_in;
   logic dl_in;
   logic extready_in;
   dp_cmd_t cmd_out;

   // DUT imodule nstantiation      
   dpc DUT_INSTANCE (.*);

  // TEST program instantiation   
   dpc_test TEST (.*);

    // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   // REF model instantiation
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic [CMDBITS-1:0] ref_cmd_out;
	 
	 dpc REF_INSTANCE(
				     .q_out(ref_cmd_out),
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
