`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;

module i2c_detector_svamod
  (
   input logic 	clk,
   input logic 	rst_n,

   input logic sda_in,
   input logic scl_in,
   input logic past_sda_in,
   input logic past_scl_in,

   input logic start_out,
   input logic stop_out,
   input logic scl_rise_out,
   input logic scl_fall_out
   );

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks (See myfilter.svh)
   ///////////////////////////////////////////////////////////////////////////////////////   

   `xcheck(sda_in);
   `xcheck(scl_in);   
   `xcheck(past_sda_in);
   `xcheck(past_scl_in);
   `xcheck(start_out);
   `xcheck(stop_out);
   `xcheck(scl_rise_out);
   `xcheck(scl_fall_out); 

   ///////////////////////////////////////////////////////////////////////////////////////
   // Property Checks
   ///////////////////////////////////////////////////////////////////////////////////////   

   property p_start;
      @(posedge clk ) disable iff (rst_n == '0)
	past_scl_in && scl_in && past_sda_in && !sda_in |-> start_out;
   endproperty

   a_start: assert property(p_start)
     else $error("i2c_detector output start_out did not show start condition.");

   property p_nostart;
      @(posedge clk ) disable iff (rst_n == '0)
	!(past_scl_in && scl_in && past_sda_in && !sda_in) |-> !start_out;
   endproperty

   a_nostart: assert property(p_nostart)
     else $error("i2c_detector output start_out showed false start condition.");


   property p_stop;
      @(posedge clk ) disable iff (rst_n == '0)
	past_scl_in && scl_in && !past_sda_in && sda_in |-> stop_out;
   endproperty

   a_stop: assert property(p_stop)
     else $error("i2c_detector output stop_out did not show stop condition.");

   property p_nostop;
      @(posedge clk ) disable iff (rst_n == '0)
	!(past_scl_in && scl_in && !past_sda_in && sda_in) |-> !stop_out;
   endproperty

   a_nostop: assert property(p_nostop)
     else $error("i2c_detector output stop_out showed false stop condition.");


   property p_scl_rise;
      @(posedge clk ) disable iff (rst_n == '0)
	scl_in && !past_scl_in |-> scl_rise_out;
   endproperty

   a_scl_rise: assert property(p_scl_rise)
     else $error("i2c_detector output scl_rise_out did not show scl_rise condition.");

   property p_noscl_rise;
      @(posedge clk ) disable iff (rst_n == '0)
	!(scl_in && !past_scl_in) |-> !scl_rise_out;
   endproperty

   a_noscl_rise: assert property(p_noscl_rise)
     else $error("i2c_detector output scl_rise_out showed false scl_rise condition.");


   property p_scl_fall;
      @(posedge clk ) disable iff (rst_n == '0)
	!scl_in && past_scl_in |-> scl_fall_out;
   endproperty

   a_scl_fall: assert property(p_scl_fall)
     else $error("i2c_detector output scl_fall_out did not show scl_fall condition.");

   property p_noscl_fall;
      @(posedge clk ) disable iff (rst_n == '0)
	!(!scl_in && past_scl_in) |-> !scl_fall_out;
   endproperty

   a_noscl_fall: assert property(p_noscl_fall)
     else $error("i2c_detector output scl_fall_out showed false scl_fall condition.");
   
   
endmodule // i2c_detector_svamod

`endif
