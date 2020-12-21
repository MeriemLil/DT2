`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;


module i2c_ctr_svamod
  
  (input logic clk,
   input logic 				     rst_n,
   input logic 				     clr_in,
   input logic 				     next_in,
   input logic 				     byteen_in, 
   input logic 				     byteok_out,
   input logic 				     frameok_out, 
   input logic [3:0] 			     bitctr_r,
   input logic [$clog2(I2C_FRAME_BYTES)-1:0] bytectr_r,
   input logic 				     seven

   );

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks
   ///////////////////////////////////////////////////////////////////////////////////////   
   
   `xcheck(clr_in);
   `xcheck(next_in);
   `xcheck(byteen_in);
   `xcheck(byteok_out);
   `xcheck(frameok_out);
   `xcheck(bitctr_r);
   `xcheck(bytectr_r);
   `xcheck(seven);

   ///////////////////////////////////////////////////////////////////////////////////////
   // Properties
   ///////////////////////////////////////////////////////////////////////////////////////   
   
   property p_stable_bitctr_r;
     @(posedge clk ) disable iff (rst_n == '0)
       !$rose(clr_in) && !next_in |=> bitctr_r == $past(bitctr_r);
   endproperty

   a_stable_bitctr_r: assert property(p_stable_bitctr_r)
     else $error("i2c_ctr variable bitctr_r not stable when !clr_in and !next_in");

   property p_stable_bytectr_r;
     @(posedge clk ) disable iff (rst_n == '0)
       !$fell(byteen_in) && !(next_in && byteen_in && seven) |=> bytectr_r == $past(bytectr_r);
   endproperty

   a_stable_bytectr_r: assert property(p_stable_bytectr_r)
     else $error("i2c_ctr variable bytectr_r not stable when it should.");
   
   property p_clr;
     @(posedge clk ) disable iff (rst_n == '0)
       clr_in |=> (bitctr_r == 0);
   endproperty

   a_clr: assert property(p_clr)
     else $error("i2c_ctr input clr_in did not clear bitctr");

   property p_byteen_false;
     @(posedge clk ) disable iff (rst_n == '0)
       !byteen_in |=> (bytectr_r == 0);
   endproperty

   a_byteen_false: assert property(p_byteen_false)
     else $error("i2c_ctr input !byteen_in did not clear bytectr");
   
   property p_next_bitctr;
     @(posedge clk ) disable iff (rst_n == '0)
       (next_in && !clr_in) && bitctr_r < 8 |=> (bitctr_r == $past(bitctr_r) + 1);
   endproperty

   a_next_bitctr: assert property(p_next_bitctr)
     else $error("i2c_ctr input next_in did cause proper incrementing of bitctr_r");

   property p_bitctr_range;
     @(posedge clk ) disable iff (rst_n == '0)
       bitctr_r >= 0 && bitctr_r <= 8;
   endproperty

   a_bitctr_range: assert property(p_bitctr_range)
     else $error("i2c_ctr variable bitctr_r not in range [0,8]");
   
   property p_next_bytectr;
     @(posedge clk ) disable iff (rst_n == '0)
       !clr_in && byteen_in && next_in && seven && bytectr_r < I2C_DATA_BYTES |=> (bytectr_r == $past(bytectr_r) + 1);
   endproperty

   a_next_bytectr: assert property(p_next_bytectr)
     else $error("i2c_ctr input next_in did cause proper incrementing of bytectr_r");

   property p_bytectr_range;
     @(posedge clk ) disable iff (rst_n == '0)
       bytectr_r >= 0 && bytectr_r <= I2C_DATA_BYTES;
   endproperty

   a_bytectr_range: assert property(p_bytectr_range)
     else $error("i2c_ctr variable bytectr_r not in range [0,%d]", I2C_DATA_BYTES);
   
   property p_seven_true;
     @(posedge clk ) disable iff (rst_n == '0)
       bitctr_r == 7 |-> seven;
   endproperty

   a_seven_true: assert property(p_seven_true)
     else $error("i2c_ctr variable seven not true when bitctr_r == 7");

   property p_seven_false;
     @(posedge clk ) disable iff (rst_n == '0)
       bitctr_r != 7 |-> !seven;
   endproperty

   a_seven_false: assert property(p_seven_false)
     else $error("i2c_ctr variable seven true when bitctr_r != 7");

   property p_frameok_true;
     @(posedge clk ) disable iff (rst_n == '0)
       (bytectr_r == I2C_DATA_BYTES) |-> frameok_out;
   endproperty

   a_frameok_true: assert property(p_frameok_true)
     else $error("i2c_ctr output frameok_out not set when bytectr_r == $d", I2C_DATA_BYTES);
   
   property p_frameok_false;
     @(posedge clk ) disable iff (rst_n == '0)
       !(bytectr_r == I2C_DATA_BYTES) |-> !frameok_out;
   endproperty

   a_frameok_false: assert property(p_frameok_false)
     else $error("i2c_ctr output frameok_out set when bytectr_r != $d", I2C_DATA_BYTES);

   ///////////////////////////////////////////////////////////////////////////////////////
   // Covergroups
   ///////////////////////////////////////////////////////////////////////////////////////   

   covergroup cg_bitctr @(posedge clk);
      coverpoint bitctr_r { 
	 bins valid[] = { [ 0:8 ] };
         bins others[] = default;
      }
   endgroup
   cg_bitctr cg_bitctr_inst = new;    

   covergroup cg_bytectr @(posedge clk);
      coverpoint bytectr_r
	{ 
	 bins valid[] = { [ 0:I2C_DATA_BYTES ] };
         bins others[] = default;
      }
   endgroup
   cg_bytectr cg_bytectr_inst = new;    
   
endmodule


`endif //  `ifndef SYNTHESIS
