`include "myfilter.svh"

import myfilter_pkg::*;

module cmem
  (input logic clk,
   input logic 			      rst_n,
   input logic 			      sde_in,
   input logic 			      sd_in,
   output logic 		      sd_out,
   input logic [$clog2(CMEMSIZE)-1:0] addr_in,
   output logic [DATABITS-1:0] 	      d_out
   );

   
endmodule 

