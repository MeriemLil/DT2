`include "myfilter.svh"
import myfilter_pkg::*;

module acc
  (input logic clk,
   input logic 		       rst_n,
   input 		       acc_cmd_t cmd_in,
   input logic [ACCBITS-1:0]   d_in,
   output logic [ACCBITS-1:0]  d_out,
   output logic [DATABITS-1:0] ext_out
   );

   
endmodule


