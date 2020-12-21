`include "myfilter.svh"
import myfilter_pkg::*;

module alu  
  (input logic clk,
   input logic 		      rst_n,
   input logic [DATABITS-1:0] m1_in,
   input logic [DATABITS-1:0] m2_in,
   input 		      alu_cmd_t cmd_in, 
   input logic [ACCBITS-1:0]  acc_in,
   output logic [ACCBITS-1:0] d_out
   );

   
endmodule

   
