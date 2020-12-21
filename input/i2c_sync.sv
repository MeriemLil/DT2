`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_sync
  
  (input logic clk,
   input logic rst_n,

   input logic sda_in,   
   input logic scl_in,

   output logic sda_out,
   output logic scl_out,

   output logic past_sda_out,
   output logic past_scl_out
   );

   
endmodule


