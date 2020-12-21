`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;

module i2c_slave_svamod
  
  (input logic clk,
   input logic rst_n,
   input logic scl_inout,
   input logic sda_inout,
   input logic ul_out,
   input logic dl_out,   
   input logic byteen, 
   input logic sde_out,
   input logic sd_out,
   input logic sd_in, 
   input logic scl,
   input logic sda,
   input logic sdaw, 
   input logic past_scl,
   input logic past_sda,
   input logic start,
   input logic stop,
   input logic scl_rise,
   input logic scl_fall,
   input logic oe,
   input logic osel,
   input logic ack,
   input logic lastbit, 
   input logic clr,
   input logic next,
   input logic byteok,
   input logic frameok,
   input logic addrok      
   );

 `include "i2c_assumes.svh"
   
   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks
   ///////////////////////////////////////////////////////////////////////////////////////   

   `xcheck(ul_out);
   `xcheck(dl_out);   
   `xcheck(sde_out);
   `xcheck(sd_out);
   `xcheck(sd_in);
   `xcheck(scl);
   `xcheck(sda);
   `xcheck(past_scl);
   `xcheck(start);
   `xcheck(stop);
   `xcheck(scl_rise);
   `xcheck(scl_fall);
   `xcheck(byteen);
   `xcheck(oe);
   `xcheck(osel);
   `xcheck(ack);
   `xcheck(next);
   `xcheck(byteok);
   `xcheck(frameok);
   `xcheck(addrok);
   `xcheck(lastbit);

   ///////////////////////////////////////////////////////////////////////////////////////
   // Property Checks
   ///////////////////////////////////////////////////////////////////////////////////////   
   
   ///////////////////////////////////////////////////////////////////////////////////////
   // i2c_sync
   ///////////////////////////////////////////////////////////////////////////////////////   

   property p_past_sda;
     @(posedge clk ) disable iff (rst_n == '0)
       $past(sda) == past_sda;
   endproperty

   a_past_sda: assert property(p_past_sda)
     else $error("i2c_slave variable past_sda did not follow sda");

   property p_past_scl;
     @(posedge clk ) disable iff (rst_n == '0)
       $past(scl) == past_scl;
   endproperty

   a_past_scl: assert property(p_past_scl)
     else $error("i2c_slave variable past_scl did not follow scl");
   
   
   ////////////////////////////////////////////////////////////////////////////////////////
   // i2c_detector
   ////////////////////////////////////////////////////////////////////////////////////////
   
   // scl_rise
   
   property p_scl_rise_true;
     @(posedge clk ) disable iff (rst_n == '0)
       scl && !past_scl |-> scl_rise;
   endproperty

   a_scl_rise_true: assert property(p_scl_rise_true)
     else $error("i2c_slave variable scl_rise in wrong state ('0)");
   c_scl_rise_true: cover property(p_scl_rise_true);

   property p_scl_rise_false;
     @(posedge clk ) disable iff (rst_n == '0)
       !(scl && !past_scl) |-> !scl_rise;
   endproperty

   a_scl_rise_false: assert property(p_scl_rise_false)
     else $error("i2c_slave variable scl_rise in wrong state ('1)");

   // scl_fall

   property p_scl_fall_true;
     @(posedge clk ) disable iff (rst_n == '0)
       !scl && past_scl |-> scl_fall;
   endproperty

   a_scl_fall_true: assert property(p_scl_fall_true)
     else $error("i2c_slave variable scl_fall in wrong state ('0)");
   c_scl_fall_true: cover property(p_scl_fall_true);

   property p_scl_fall_false;
     @(posedge clk ) disable iff (rst_n == '0)
       !(!scl && past_scl) |-> !scl_fall;
   endproperty

   a_scl_fall_false: assert property(p_scl_fall_false)
     else $error("i2c_slave variable scl_fall in wrong state ('1)");

   // scl rise and fall mutex
   
   property p_scl_rise_fall_mutex;
     @(posedge clk ) disable iff (rst_n == '0)
       !(scl_rise && scl_fall);
   endproperty

   a_scl_rise_fall_mutex: assert property(p_scl_rise_fall_mutex)
     else $error("i2c_slave variables scl_rise and scl_fall in state 1 at the same time.");

   // start

   property p_start_true;
     @(posedge clk ) disable iff (rst_n == '0)
       scl && past_sda && !sda |-> start;
   endproperty

   a_start_true: assert property(p_start_true)
     else $error("i2c_slave variable start in wrong state ('0)");
   c_start_true: cover property(p_start_true);


   property p_start_false;
     @(posedge clk ) disable iff (rst_n == '0)
       !(scl && past_sda && !sda) |-> !start;
   endproperty

   a_start_false: assert property(p_start_false)
     else $error("i2c_slave variable start in wrong state ('1)");

   // stop

   property p_stop_true;
     @(posedge clk ) disable iff (rst_n == '0)
       scl && !past_sda && sda |-> stop;
   endproperty

   a_stop_true: assert property(p_stop_true)
     else $error("i2c_slave variable stop in wrong state ('0)");
   c_stop_true: cover property(p_stop_true);
   
   property p_stop_false;
     @(posedge clk ) disable iff (rst_n == '0)
       !(scl && !past_sda && sda) |-> !stop;
   endproperty

   a_stop_false: assert property(p_stop_false)
     else $error("i2c_slave variable stop in wrong state ('1)");

   // start stop mutex
   
   property p_scl_start_stop_mutex;
     @(posedge clk ) disable iff (rst_n == '0)
       !(start && stop);
   endproperty

   a_scl_start_stop_mutex: assert property(p_scl_start_stop_mutex)
     else $error("i2c_slave variables start and stop in state 1 at the same time.");
   
   ////////////////////////////////////////////////////////////////////////////////////////
   // i2c_srg
   ////////////////////////////////////////////////////////////////////////////////////////

   property p_lastbit;
     @(posedge clk ) disable iff (rst_n == '0)
       !clr && next |=> lastbit == $past(sda);
   endproperty

   a_lastbit: assert property(p_lastbit)
     else $error("i2c_slave variable sda not transferred to lastbit");
      
   ////////////////////////////////////////////////////////////////////////////////////////
   // i2c_fsm
   ////////////////////////////////////////////////////////////////////////////////////////

   // next pulse width
   
   property p_next;
     @(posedge clk ) disable iff (rst_n == '0)
       $rose(next) |=> $fell(next);
   endproperty

   a_next: assert property(p_next)
     else $error("i2c_slave variable next was 1 for more than one cycle");
   c_next: cover property(p_next);

   // Slave ACK length

   property p_slave_ack;
     @(posedge clk ) disable iff (rst_n == '0)
       $rose(oe) && !osel |=> ((oe && !osel) throughout (!scl_fall [* 1:$]));
   endproperty

   a_slave_ack: assert property(p_slave_ack)
     else $error("i2c_slave variable oe not 1 throughout slave ACK period.");
   c_slave_ack: cover property(p_slave_ack);
   

endmodule

`endif //  `ifndef SYNTHESIS
