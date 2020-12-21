`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;

module acc_svamod
  
  (input logic clk,
   input logic 		      rst_n,
   input 		      acc_cmd_t cmd_in,
   input logic [ACCBITS-1:0]  d_in,
   input logic [ACCBITS-1:0]  d_out,
   input logic [DATABITS-1:0] ext_out,
   logic signed [ACCBITS-1:0] acc_r
   );

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks (See myfilter.svh)
   ///////////////////////////////////////////////////////////////////////////////////////   

   `xcheck(cmd_in);
   `xcheck(d_in);
   `xcheck(d_out);
   `xcheck(ext_out);
   `xcheck(acc_r);

   ///////////////////////////////////////////////////////////////////////////////////////
   // Property Checks
   ///////////////////////////////////////////////////////////////////////////////////////   
   
   property p_stable_acc_r;
     @(posedge clk ) disable iff (rst_n == '0)
       !((cmd_in == ACC_LOAD) || (cmd_in == ACC_CLEAR)) |=> acc_r == $past(acc_r);
   endproperty

   a_stable_acc_r: assert property(p_stable_acc_r)
     else $error("acc variable acc_r not stable when cmd_in is not ACC_LOAD or ACC_CLEAR");

   property p_ACC_LOAD;
     @(posedge clk ) disable iff (rst_n == '0)
       (cmd_in == ACC_LOAD) |=> (acc_r == $past(d_in));
   endproperty

   a_ACC_LOAD: assert property(p_ACC_LOAD)
     else $error("acc variable acc_r not loaded with ACC_LOAD");

   property p_ACC_CLEAR;
     @(posedge clk ) disable iff (rst_n == '0)
       (cmd_in == ACC_CLEAR) |=> (acc_r == 0);
   endproperty

   a_ACC_CLEAR: assert property(p_ACC_CLEAR)
     else $error("acc variable acc_r not zero after ACC_CLEAR");

   property p_d_out;
     @(posedge clk ) disable iff (rst_n == '0)
       d_out == acc_r;
   endproperty

   a_d_out: assert property(p_d_out)
     else $error("acc output d_out not equal to variable acc_r.");

   property p_ext_out;
     @(posedge clk ) disable iff (rst_n == '0)
       ext_out == acc_r[DATABITS-1:0];
   endproperty

   a_ext_out: assert property(p_ext_out)
     else $error("acc output ext_out not equal to acc_r[DATABITS-1:0].");
      
endmodule
   


`endif
