`include "myfilter.svh"
import myfilter_pkg::*;

`ifndef SYNTHESIS

module acc_tb  #(parameter DUT_VS_REF_SIMULATION = 0);

   // Testbench signals   
   logic clk;
   logic rst_n;
   acc_cmd_t cmd_in;
   logic [ACCBITS-1:0] d_in;
   logic [ACCBITS-1:0] d_out;
   logic [DATABITS-1:0] ext_out;

   // DUT module instantiation   
   acc DUT_INSTANCE (.*);

  // TEST program  instantiation   
   acc_test TEST (.*);

    // Bind assertion module   
 `include "myfilter_svabind.svh"
   
   // REF model instantiation
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL

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

   initial
     begin : reset_gen
	rst_n = '0;
	@(negedge clk);
	rst_n = '1;
     end : reset_gen
endmodule


   
`endif

