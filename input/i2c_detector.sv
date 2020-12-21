`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_detector
  (
   input logic 	clk,
   input logic 	rst_n,

   input logic 	sda_in,
   input logic 	scl_in,
   input logic 	past_sda_in,
   input logic 	past_scl_in,

   output logic start_out,
   output logic stop_out,
   output logic scl_rise_out,
   output logic scl_fall_out
   );


endmodule

