`ifndef SYNTHESIS

`include "myfilter.svh"
import myfilter_pkg::*;
import i2c_pkg::*;

module myfilter_tb #(parameter DUT_VS_REF_SIMULATION = 0);
   
   logic clk;
   logic rst_n;
   tri1  scl_inout;
   tri1  sda_inout;   
   logic [DATABITS-1:0] ext_in;
   logic 		extready_in;
   logic [DATABITS-1:0] ext_out;
   logic 		extvalid_out;
   i2c_if i2c_bus(scl_inout, sda_inout);

   initial
     begin
	clk = '0;
	forever #(CLK_PERIOD/2) clk = ~clk;
     end
   
   initial
     begin
	rst_n = '0;
	@(negedge clk);
	@(negedge clk);	
	rst_n = '1;
     end

   // DUT instantiation
   myfilter DUT_INSTANCE (.*);

   // Assertion module binding file inclusion
`include "myfilter_svabind.svh"   

   // Test program instantiation   
   myfilter_test TEST (.*);
   
   generate
      if (DUT_VS_REF_SIMULATION) begin : REF_MODEL
	 tri1 ref_scl_inout;
	 tri1 ref_sda_inout;
	 logic ref_extready_in;	 
	 logic [DATABITS-1:0] ref_ext_in;
	 logic ref_extvalid_out;
	 logic [DATABITS-1:0] ref_ext_out;
	 i2c_if ref_i2c_bus(ref_scl_inout, ref_sda_inout);
	 
	 myfilter REF_INSTANCE
	   (.clk(clk),
	    .rst_n(rst_n),
	    .scl_inout(ref_scl_inout),
	    .sda_inout(ref_sda_inout),
	    .ext_in(ref_ext_in),
	    .extready_in(ref_extready_in),	    
	    .extvalid_out(ref_extvalid_out),
	    .ext_out(ref_ext_out)
	    );

	 myfilter_test REF_TEST
	   (.clk(clk),
	    .rst_n(rst_n),
	    .i2c_bus(ref_i2c_bus),
	    .ext_in(ref_ext_in),
	    .extready_in(ref_extready_in),	    
	    .extvalid_out(ref_extvalid_out),
	    .ext_out(ref_ext_out)
	    );

      end 
   endgenerate
   
endmodule 



`endif
