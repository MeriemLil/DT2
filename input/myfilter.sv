`include "myfilter.svh"
import myfilter_pkg::*;

module myfilter
  
  (input logic clk,
   input logic 		       rst_n,
   inout tri 		       scl_inout,
   inout tri 		       sda_inout,
   input logic [DATABITS-1:0]  ext_in,
   input logic 		       extready_in,
   output logic [DATABITS-1:0] ext_out,
   output logic 	       extvalid_out
   );

   logic 	       sde;
   logic 	       sdin;
   logic 	       ul;
   logic 	       dl;   
   logic 	       sdout;      
   logic 	       srst_n;

   i2c_slave i2c_slave_1
     (
      .clk(clk),
      .rst_n(srst_n),
      .scl_inout(scl_inout),
      .sda_inout(sda_inout),
      .ul_out(ul),
      .dl_out(dl),      
      .sde_out(sde),
      .sd_out(sdin),
      .sd_in(sdout)
      );
   

   filter_unit filter_unit_1
     (
      .clk(clk),
      .rst_n(srst_n),
      .sde_in(sde),
      .sd_in(sdin),
      .sd_out(sdout),
      .ul_in(ul),
      .dl_in(dl),      
      .extready_in(extready_in),
      .ext_in(ext_in),
      .extvalid_out(extvalid_out),      
      .ext_out(ext_out)
      );


   reset_sync reset_sync_1
     (
      .clk(clk),
      .rst_n(rst_n),
      .srst_n(srst_n)
      );
     
	
endmodule


