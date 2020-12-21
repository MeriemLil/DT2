`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;

module i2c_sync_svamod
  (
   input logic clk,
   input logic rst_n,
   input logic sda_in, 
   input logic scl_in,
   input logic sda_out,
   input logic scl_out,
   input logic past_sda_out,
   input logic past_scl_out,
   input logic sda_sff1_r,
   input logic sda_sff2_r,
   input logic scl_sff1_r,
   input logic scl_sff2_r, 
   input logic past_sda_r,
   input logic past_scl_r
   );

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks (See myfilter.svh)
   ///////////////////////////////////////////////////////////////////////////////////////   

   X_sda_in: assert property ( @(posedge clk) disable iff (rst_n !== '1) (sda_in !== 'x))
     else $error("i2c_sync port sda_in in unknown state");
   X_scl_in: assert property ( @(posedge clk) disable iff (rst_n !== '1) (scl_in !== 'x))
     else $error("i2c_sync port scl_in in unknown state");
   
   `xcheck(sda_out);
   `xcheck(scl_out);
   `xcheck(past_sda_out);
   `xcheck(past_scl_out);
   `xcheck(sda_sff1_r);
   `xcheck(sda_sff2_r);
   `xcheck(scl_sff1_r);
   `xcheck(scl_sff2_r); 
   `xcheck(past_sda_r);
   `xcheck(past_scl_r);

   ///////////////////////////////////////////////////////////////////////////////////////
   // Property Checks
   ///////////////////////////////////////////////////////////////////////////////////////   

   property p_scl_sync;
      @(posedge clk ) disable iff (rst_n == '0)
	(scl_sff2_r == $past(scl_sff1_r)) &&  (past_scl_r == $past(scl_sff2_r));
   endproperty

   a_scl_sync: assert property(p_scl_sync)
     else $error("i2c_sync scl flip-flops error");

   property p_sda_sync;
      @(posedge clk ) disable iff (rst_n == '0)
	(sda_sff2_r == $past(sda_sff1_r)) &&  (past_sda_r == $past(sda_sff2_r));
   endproperty

   a_sda_sync: assert property(p_sda_sync)
     else $error("i2c_sync sda flip-flops error");

endmodule // i2c_sync_svamod

`endif
