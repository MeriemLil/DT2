`include "myfilter.svh"
import myfilter_pkg::*;

module dmem
  (input logic clk,
   input logic 			      rst_n,
   input logic 			      sde_in,
   input logic 			      sd_in,
   output logic 		      sd_out,
   input 			      dmem_cmd_t cmd_in,
   input logic [$clog2(DMEMSIZE)-1:0] addr_in,
   input logic [DATABITS-1:0] 	      d_in,
   input logic [DATABITS-1:0] 	      ext_in,   
   output logic [DATABITS-1:0] 	      d_out
   );


endmodule 

