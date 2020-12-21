`include "myfilter.svh"

import myfilter_pkg::*;

`ifndef SYNTHESIS

module i2c_srg_svamod
  
  (input logic clk,
   input logic 	rst_n,
   input logic 	clr_in,
   input logic 	next_in,
   input logic 	bit_in,
   input logic bit_out,
   input logic addrok_out,
   input logic [7:0] 	srg_r
   );
   
   assert property ( @(posedge clk) disable iff (rst_n !== '1) !$isunknown(clr_in))
     else $error("i2c_srg port clr_in has unknown bits");
   assert property ( @(posedge clk) disable iff (rst_n !== '1) !$isunknown(next_in))
     else $error("i2c_srg port next_in has unknown bits");
   assert property ( @(posedge clk) disable iff (rst_n !== '1) !$isunknown(bit_in))
     else $error("i2c_srg port bit_in has unknown bits");
   assert property ( @(posedge clk) disable iff (rst_n !== '1) !$isunknown(bit_out))
     else $error("i2c_srg port bit_out has unknown bits");
   assert property ( @(posedge clk) disable iff (rst_n !== '1) !$isunknown(addrok_out))
     else $error("i2c_srg port addrok_out has unknown bits");
   assert property ( @(posedge clk) disable iff (rst_n !== '1) !$isunknown(srg_r))
     else $error("i2c_srg variable srg_r has unknown bits");

   property p_stable_srg_r;
     @(posedge clk ) disable iff (rst_n == '0)
       !$rose(clr_in) && !next_in |=> srg_r == $past(srg_r);
   endproperty

   a_stable_srg_r: assert property(p_stable_srg_r)
     else $error("i2c_srg variable srg_r not stable when !clr_in and !next_in");
   
   property p_clr;
     @(posedge clk ) disable iff (rst_n == '0)
       clr_in |=> srg_r == 8'b00000000;
   endproperty

   a_clr: assert property(p_clr)
     else $error("i2c_srg input clr_in did not clear srg_r");

   property p_next;
     @(posedge clk ) disable iff (rst_n == '0)
       (next_in && !clr_in) |=> srg_r == { $past(srg_r[6:0]), $past(bit_in) };
   endproperty

   a_next: assert property(p_next)
     else $error("i2c_srg input next_in did cause proper shifting of srg_r");

   property p_bit_out;
     @(posedge clk ) disable iff (rst_n == '0)
       srg_r[0] |-> bit_out;
   endproperty

   a_bit_out: assert property(p_bit_out)
     else $error("i2c_srg output bit_out did not follow srg_r[0]");

   property p_addrok_true;
     @(posedge clk ) disable iff (rst_n == '0)
       (srg_r[7:1] == I2C_ADDRESS) |-> addrok_out;
   endproperty

   a_addrok_true: assert property(p_addrok_true)
     else $error("i2c_srg output addrok_out not set when I2C_ADDRESS was ok");

   property p_addrok_false;
     @(posedge clk ) disable iff (rst_n == '0)
       !(srg_r[7:1] == I2C_ADDRESS) |-> !addrok_out;
   endproperty

   a_addrok_false: assert property(p_addrok_false)
     else $error("i2c_srg output addrok_out set when I2C_ADDRESS was not ok");
   
endmodule


`endif //  `ifndef SYNTHESIS
