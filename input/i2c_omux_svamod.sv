`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;


module i2c_omux_svamod  
  (
   input logic 	clk,
   input logic 	rst_n,
   input logic 	oe_in,
   input logic 	osel_in,
   input logic 	ack_in,
   input logic 	sd_in,
   input logic  sdaw_out
   );

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks (See myfilter.svh)
   ///////////////////////////////////////////////////////////////////////////////////////   
   
   `xcheck(oe_in);
   `xcheck(osel_in);
   `xcheck(ack_in);
   `xcheck(sd_in);
   assert property ( @(posedge clk) disable iff (rst_n !== '1) (sdaw_out !== 'x))
     else $error("i2c_slave port sdaw_out in unknown state.");

   ///////////////////////////////////////////////////////////////////////////////////////
   // Property Checks
   ///////////////////////////////////////////////////////////////////////////////////////   

   property p_oe_trix;
     @(posedge clk ) disable iff (rst_n == '0)
       !oe_in |-> sdaw_out === 'z;
   endproperty

   a_oe_trix: assert property(p_oe_trix)
     else $error("i2c_omux output sdaw_out not put to hi-Z state when oe_in == '0");

   property p_ack_enc0;
     @(posedge clk ) disable iff (rst_n == '0)
       oe_in && !osel_in && !ack_in  |-> sdaw_out === '0;
   endproperty

   a_ack_enc0: assert property(p_ack_enc0)
     else $error("i2c_omux output sdaw_out not put to 0-state when when oe, osel, ack == 100");

   property p_ack_enc1;
     @(posedge clk ) disable iff (rst_n == '0)
       oe_in && !osel_in && ack_in  |-> sdaw_out === 'z;
   endproperty

   a_ack_enc1: assert property(p_ack_enc1)
     else $error("i2c_omux output sdaw_out not put to hi-Z state when when oe, osel, ack == 101");

   property p_sd_enc0;
     @(posedge clk ) disable iff (rst_n == '0)
       oe_in && osel_in && !sd_in  |-> sdaw_out === '0;
   endproperty

   a_sd_enc0: assert property(p_sd_enc0)
     else $error("i2c_omux output sdaw_out not put to 0-state when when oe, osel, sd == 110");

   property p_sd_enc1;
     @(posedge clk ) disable iff (rst_n == '0)
       oe_in && osel_in && sd_in  |-> sdaw_out === 'z;
   endproperty

   a_sd_enc1: assert property(p_sd_enc1)
     else $error("i2c_omux output sdaw_out not put to hi-Z state when when oe, osel, sd == 111");
   
   
endmodule

`endif //  `ifndef SYNTHESIS
