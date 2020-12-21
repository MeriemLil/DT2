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

   always_comb
     begin
	if (past_sda_in == 1 && past_scl_in == 1 && sda_in == 0 && scl_in == 1)
	  start_out = 1;
	else
	  start_out = 0;

	if (past_sda_in == 0 && past_scl_in == 1 && sda_in == 1 && scl_in == 1)
	  stop_out = 1;
	else
	  stop_out = 0;

	if (past_scl_in == 0 && scl_in == 1)
	  scl_rise_out = 1;
	else
	  scl_rise_out = 0;

	if (past_scl_in == 1 && scl_in == 0)
	  scl_fall_out = 1;
	else
	  scl_fall_out = 0;
     end


endmodule

