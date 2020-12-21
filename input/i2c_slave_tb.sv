`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;

module i2c_slave_tb  #(parameter DUT_VS_REF_SIMULATION = 0);

   logic clk;
   logic rst_n;
   tri1  scl_inout;
   tri1  sda_inout;
   logic sde_out;
   logic sd_out;
   logic sd_in;
   logic ul_out;
   logic dl_out;   
   i2c_if i2c_bus(scl_inout, sda_inout);
   
   // DUT module instantiation
   i2c_slave DUT_INSTANCE (.*);

   // TEST program instantiation
   i2c_slave_test TEST (.*);   
   
    // Bind assertion module   
 `include "myfilter_svabind.svh"
    
   // Clock generator
   always
     begin
	if (clk == '0)
	  clk = '1;
	else
	  clk = '0;
	#(CLK_PERIOD/2.0);
     end
   
   // Reset generator
   initial
     begin
	rst_n = '0;
	@(negedge clk);
	@(negedge clk);	
	rst_n = '1;
     end


   // Reference module instantiation   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 tri1 	 ref_scl_inout;
	 tri1 	 ref_sda_inout;
	 logic 	 ref_sd_in;
	 logic 	 ref_sd_out;
	 logic 	 ref_ul_out;
	 logic 	 ref_dl_out;	 
	 i2c_if ref_i2c_bus(ref_scl_inout, ref_sda_inout);	 

	 // Reference module instantiation	 
	 i2c_slave REF_INSTANCE(.clk(clk),
				.rst_n(rst_n),
				.scl_inout(ref_scl_inout),
				.sda_inout(ref_sda_inout),
				.sde_out(ref_sde_out),
				.sd_in(ref_sd_in),
				.sd_out(ref_sd_out),
				.ul_out(ref_ul_out),
				.dl_out(ref_dl_out)				
				);

	 // Test program instantiation
	 i2c_slave_test REF_TEST (.clk(clk),
				  .rst_n(rst_n),
				  .i2c_bus(ref_i2c_bus),
				  .sde_out(ref_sde_out),
				  .sd_in(ref_sd_in),
				  .sd_out(ref_sd_out),
				  .ul_out(ref_ul_out),
				  .dl_out(ref_dl_out)				  
				  );
	 

	 // Output comparison

	 always @(posedge clk)
	   begin : checker_proc
	      assert(sde_out == ref_sde_out)
		else $warning("sde_out values differ.");
	      assert(ul_out == ref_ul_out)
		else $warning("ul_out values differ.");
	      assert(dl_out == ref_dl_out)
		else $warning("dl_out values differ.");
	      assert(sd_out == ref_sd_out)
		else $warning("sd_out values differ.");
	   end : checker_proc

      end 
   endgenerate
   
endmodule

`endif
