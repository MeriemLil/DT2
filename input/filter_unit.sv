`include "myfilter.svh"
import myfilter_pkg::*;

module filter_unit
  
  (input logic clk,
   input logic 		       rst_n,
   input logic 		       sde_in,
   input logic 		       sd_in, 
   output logic 	       sd_out, 
   input logic 		       ul_in,
   input logic 		       dl_in,   
   input logic [DATABITS-1:0]  ext_in,
   input logic 		       extready_in,
   output logic [DATABITS-1:0] ext_out,
   output logic 	       extvalid_out
   );

   
endmodule


