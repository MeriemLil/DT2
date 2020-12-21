`ifndef SYNTHESIS
`include "myfilter.svh"
import myfilter_pkg::*;

module reset_sync_tb  #(parameter DUT_VS_REF_SIMULATION = 0);

   // Testbench signals
   
   logic clk;
   logic rst_n;
   logic srst_n;   

   // DUT instantiation   
   reset_sync DUT_INSTANCE (.*);


  // Test program
   initial
     begin : test_program
	clk = '0;
	rst_n = '1;
	#(CLK_PERIOD/2);

	$info("T1: ASYNC RESET");
	clk = '1;
	#(CLK_PERIOD/2);
	clk = '0;
	#(CLK_PERIOD/4);	
	rst_n = '0;
	#(CLK_PERIOD/4);
	clk = '1;
	#(CLK_PERIOD/2);
	clk = '0;
	#(CLK_PERIOD/4);		
	rst_n = '1;
	#(CLK_PERIOD/4);

	repeat(5)
	  begin
	     clk = '1;
	     #(CLK_PERIOD/2);
	     clk = '0;
	     #(CLK_PERIOD/2);
	  end


	$info("T2: RECOVERY VIOLATION");
	clk = '1;
	#(CLK_PERIOD/2);
	clk = '0;
	rst_n = '0;
	#(CLK_PERIOD/2);
	clk = '1;
	#(CLK_PERIOD/2);
	clk = '0;
	#(CLK_PERIOD/2-0.001ns);
	rst_n = '1;
	#(0.001ns)

	repeat(5)
	  begin
	     clk = '1;
	     #(CLK_PERIOD/2);
	     clk = '0;
	     #(CLK_PERIOD/2);
	  end

	$info("T2: REMOVAL VIOLATION");
	clk = '1;
	#(CLK_PERIOD/2);
	clk = '0;
	rst_n = '0;
	#(CLK_PERIOD/2);
	clk = '1;
	#(CLK_PERIOD/2);
	clk = '0;
	#(CLK_PERIOD/2);
	clk = '1;	
	#(0.045ns)
	rst_n = '1;
	#(CLK_PERIOD/2-0.045ns);

	repeat(5)
	  begin
	     #(CLK_PERIOD/2);
	     clk = '0;
	     #(CLK_PERIOD/2);
	     clk = '1;

	  end
	
     end : test_program

   // REF model instantiation
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 logic ref_srst_n;
	 reset_sync REF_INSTANCE (.srst_n(ref_srst_n), .*);
      end 
   endgenerate

endmodule // reset_sync_tb

`endif
