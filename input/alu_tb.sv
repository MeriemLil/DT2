`ifndef SYNTHESIS

`include "myfilter.svh"
import myfilter_pkg::*;

module alu_tb #(parameter DUT_VS_REF_SIMULATION = 0);
   logic clk;
   logic rst_n;
   logic [DATABITS-1:0] m1_in;
   logic [DATABITS-1:0] m2_in;
   alu_cmd_t cmd_in;
   logic [ACCBITS-1:0] acc_in;
   logic [ACCBITS-1:0] d_out;

  // DUT module instantiation
   alu DUT_INSTANCE (.*);

  // TEST program instantiation   
   alu_test TEST (.*);

    // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic [ACCBITS-1:0] 	ref_d_out;
	 alu REF_INSTANCE(.mul_out(ref_d_out),
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
