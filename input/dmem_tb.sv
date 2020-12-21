`ifndef SYNTHESIS

`include "myfilter.svh"
import myfilter_pkg::*;

module dmem_tb #(parameter DUT_VS_REF_SIMULATION = 0);

   logic clk;
   logic rst_n;
   logic sde_in;
   logic sd_in;
   logic sd_out;
   dmem_cmd_t                   cmd_in;
   logic [$clog2(DMEMSIZE)-1:0] addr_in;
   logic [DATABITS-1:0] 	d_in;
   logic [DATABITS-1:0] 	ext_in;   
   logic [DATABITS-1:0] 	d_out;

   // DUT module instantiation      
   dmem DUT_INSTANCE (.*);

  // TEST program instantiation   
   dmem_test TEST (.*);

    // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   // REF model instantiation
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic ref_sd_out;
	 logic [DATABITS-1:0] ref_d_out;
	 
	 dmem REF_INSTANCE(.sd_out(ref_sd_out),
			    .d_out(ref_d_out),
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
