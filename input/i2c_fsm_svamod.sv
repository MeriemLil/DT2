`include "myfilter.svh"

import myfilter_pkg::*;

`ifndef SYNTHESIS

module i2c_fsm_svamod
  (
   input logic clk,
   input logic rst_n,
   input logic start_in,
   input logic stop_in,
   input logic scl_rise_in,
   input logic scl_fall_in,
   input logic addrok_in,
   input logic byteok_in,
   input logic frameok_in,
   input logic lastbit_in,
   input logic ul_out,
   input logic dl_out,
   input logic byteen_out,      
   input logic sde_out, 
   input logic clr_out, 
   input logic next_out,
   input logic oe_out,
   input logic osel_out,
   input logic ack_out,
   input       i2c_fsm_t state_r, 
   input       i2c_fsm_t next_state  
   );

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks
   ///////////////////////////////////////////////////////////////////////////////////////   
   
   `xcheck(start_in);
   `xcheck(stop_in);
   `xcheck(scl_rise_in);
   `xcheck(scl_fall_in);
   `xcheck(addrok_in);
   `xcheck(byteok_in);
   `xcheck(frameok_in);
   `xcheck(lastbit_in);
   `xcheck(ul_out);
   `xcheck(dl_out);
   `xcheck(byteen_out);      
   `xcheck(sde_out);
   `xcheck(oe_out);
   `xcheck(osel_out);
   `xcheck(ack_out);
   `xcheck(clr_out);
   `xcheck(next_out);
   `xcheck(state_r);
   `xcheck(next_state);

   ///////////////////////////////////////////////////////////////////////////////////////
   // Property Checks
   ///////////////////////////////////////////////////////////////////////////////////////   
   
   /////////////////////////////////////////////////////////////////////////////////////   
   // IDLE
   /////////////////////////////////////////////////////////////////////////////////////

   // Transitions
   
   property p_IDLE_a;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == IDLE) && start_in |=> state_r == HRX;
   endproperty

   a_IDLE_a: assert property(p_IDLE_a)
     else $error("i2c_fsm IDLE-a");

   property p_IDLE_default;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == IDLE) && !start_in |=> state_r == IDLE;
   endproperty

   a_IDLE_default: assert property(p_IDLE_default)
     else $error("i2c_fsm did not stay in IDLE");

   // Outputs

   property p_IDLE_moore;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == IDLE) |-> (!ack_out && !ul_out && !dl_out && !byteen_out && clr_out && !next_out && !oe_out && !osel_out && !sde_out );
   endproperty

   a_IDLE_moore: assert property(p_IDLE_moore)
     else $error("i2c_fsm IDLE-moore");
   
   /////////////////////////////////////////////////////////////////////////////////////      
   // HRX
   /////////////////////////////////////////////////////////////////////////////////////

   // Transitions

   property p_HRX_a;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HRX) && stop_in |=> (state_r == IDLE);
   endproperty

   a_HRX_a: assert property(p_HRX_a)
     else $error("i2c_fsm HRX-a");

   property p_HRX_b_c;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HRX) && !stop_in && scl_rise_in |=> (state_r == HRX);
   endproperty

   a_HRX_b_c: assert property(p_HRX_b_c)
     else $error("i2c_fsm HRX-b-c");

   property p_HRX_b_d_e;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HRX) && !stop_in && !scl_rise_in && (byteok_in && scl_fall_in) |=> (state_r == HACK);
   endproperty

   a_HRX_b_d_e: assert property(p_HRX_b_d_e)
     else $error("i2c_fsm HRX-b-d-e");

   property p_HRX_b_d_f;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HRX) && !stop_in && !scl_rise_in && !(byteok_in && scl_fall_in) |=> (state_r == HRX);
   endproperty

   a_HRX_b_d_f: assert property(p_HRX_b_d_f)
     else $error("i2c_fsm HRX-b-d-f");
   
   property p_HRX_default;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HRX) && !(stop_in || (!scl_rise_in && byteok_in && scl_fall_in)) |=> (state_r == HRX);
   endproperty

   a_HRX_default: assert property(p_HRX_default)
     else $error("i2c_fsm did not stay in HRX");

   // Outputs

   property p_HRX_moore;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HRX) |-> (!ack_out && !ul_out && !dl_out && !byteen_out && !clr_out && !oe_out && !osel_out && !sde_out );
   endproperty

   a_HRX_moore: assert property(p_HRX_moore)
     else $error("i2c_fsm IDLE-moore");

   property p_HRX_mealy_b_c;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HRX) && !stop_in && scl_rise_in |-> next_out;
   endproperty

   a_HRX_mealy_b_c: assert property(p_HRX_mealy_b_c)
     else $error("i2c_fsm HRX-mealy-b-c");

   property p_HRX_mealy_b_d;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HRX) && !stop_in && !scl_rise_in |-> !next_out;
   endproperty

   a_HRX_mealy_b_d: assert property(p_HRX_mealy_b_d)
     else $error("i2c_fsm HRX-mealy-b-d");
   
   /////////////////////////////////////////////////////////////////////////////////////      
   // HACK
   /////////////////////////////////////////////////////////////////////////////////////

   // Transitions

   property p_HACK_a;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HACK) && stop_in |=> (state_r == IDLE);
   endproperty

   a_HACK_a: assert property(p_HACK_a)
     else $error("i2c_fsm HACK-a");

   property p_HACK_b_d_h;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HACK) && !stop_in && !addrok_in && !scl_fall_in |=> (state_r == HACK);
   endproperty

   a_HACK_b_d_h: assert property(p_HACK_b_d_h)
     else $error("i2c_fsm HACK-b-d-h");

   property p_HACK_b_c_f;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HACK) && !stop_in && addrok_in && !scl_fall_in |=> (state_r == HACK);
   endproperty

   a_HACK_b_c_f: assert property(p_HACK_b_c_f)
     else $error("i2c_fsm HACK-b-c-f");
   
   property p_HACK_b_c_e_j;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HACK) && !stop_in && addrok_in & scl_fall_in && !lastbit_in  |=> (state_r == RX);
   endproperty

   a_HACK_b_c_e_j: assert property(p_HACK_b_c_e_j)
     else $error("i2c_fsm HACK-b-c-e-j");

   property p_HACK_b_c_e_i;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HACK) && !stop_in && addrok_in && scl_fall_in && lastbit_in |=> (state_r == TX);
   endproperty

   a_HACK_b_c_e_i: assert property(p_HACK_b_c_e_i)
     else $error("i2c_fsm HACK-b-c-e-i");

   property p_HACK_default;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HACK) && !(stop_in || scl_fall_in) |=> (state_r == HACK);
   endproperty

   a_HACK_default: assert property(p_HACK_default)
     else $error("i2c_fsm HACK-default");

   // Outputs

   property p_HACK_moore;
      @(posedge clk ) disable iff (rst_n == '0)
	(state_r == HACK) |-> (!ul_out && !next_out && !osel_out && !sde_out );
   endproperty

   a_HACK_moore: assert property(p_HACK_moore)
     else $error("i2c_fsm HACK-moore");

   property p_HACK_mealy_b_d;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HACK) && !stop_in && !addrok_in |-> !clr_out && !oe_out && ack_out;
   endproperty

   a_HACK_mealy_b_d: assert property(p_HACK_mealy_b_d)
     else $error("i2c_fsm HACK-mealy-b-d");

   property p_HACK_mealy_b_c;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HACK) && !stop_in && addrok_in |-> oe_out && !ack_out;
   endproperty

   a_HACK_mealy_b_c: assert property(p_HACK_mealy_b_c)
     else $error("i2c_fsm HACK-mealy-b-c");

   property p_HACK_mealy_b_c_f;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HACK) && !stop_in && addrok_in && !scl_fall_in |-> !clr_out;
   endproperty

   a_HACK_mealy_b_c_f: assert property(p_HACK_mealy_b_c_f)
     else $error("i2c_fsm HACK-mealy-b-c-f");

   property p_HACK_mealy_b_c_e;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == HACK) && !stop_in && addrok_in && scl_fall_in |-> clr_out;
   endproperty

   a_HACK_mealy_b_c_e: assert property(p_HACK_mealy_b_c_e)
     else $error("i2c_fsm HACK-mealy-b-c-e");
   
   /////////////////////////////////////////////////////////////////////////////////////   
   // RX
   /////////////////////////////////////////////////////////////////////////////////////

   // Transitions

   property p_RX_a;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RX) && stop_in |=> (state_r == IDLE);
   endproperty

   a_RX_a: assert property(p_RX_a)
     else $error("i2c_fsm RX-a");

   property p_RX_b_c;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RX) && !stop_in && scl_rise_in |=> (state_r == RX);
   endproperty

   a_RX_b_c: assert property(p_RX_b_c)
     else $error("i2c_fsm RX-b-c");

   property p_RX_b_d_f;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RX) && !stop_in && !scl_rise_in && !scl_fall_in |=> (state_r == RX);
   endproperty

   a_RX_b_d_f: assert property(p_RX_b_d_f)
     else $error("i2c_fsm RX-b-d-f");

   property p_RX_b_d_e_h;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RX) && !stop_in && !scl_rise_in && scl_fall_in & !byteok_in |=> (state_r == RX);
   endproperty

   a_RX_b_d_e_h: assert property(p_RX_b_d_e_h)
     else $error("i2c_fsm RX-b-d-e-h");

   property p_RX_b_d_e_g;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RX) && !stop_in && !scl_rise_in && scl_fall_in & byteok_in |=> (state_r == RACK);
   endproperty

   a_RX_b_d_e_g: assert property(p_RX_b_d_e_g)
     else $error("i2c_fsm RX-b-d-e-g");

   property p_RX_default;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RX) && !(stop_in || (!scl_rise_in && scl_fall_in & byteok_in)) |=> (state_r == RX);
   endproperty

   a_RX_default: assert property(p_RX_default)
     else $error("i2c_fsm RX-default");

   // Outputs

   property p_RX_moore;
      @(posedge clk ) disable iff (rst_n == '0)
	(state_r == RX) |-> (!ack_out && !clr_out && ul_out && !dl_out && byteen_out && !oe_out && !osel_out  );
   endproperty

   a_RX_moore: assert property(p_RX_moore)
     else $error("i2c_fsm RX-moore");

   property p_RX_mealy_b_c;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RX) && !stop_in && scl_rise_in |-> next_out;
   endproperty

   a_RX_mealy_b_c: assert property(p_RX_mealy_b_c)
     else $error("i2c_fsm RX-mealy-b-c");

   property p_RX_mealy_b_d;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RX) && !stop_in && !scl_rise_in |-> !next_out;
   endproperty

   a_RX_mealy_b_d: assert property(p_RX_mealy_b_d)
     else $error("i2c_fsm RX-mealy-b-d");

   property p_RX_mealy_b_d_f;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RX) && !stop_in && !scl_rise_in && !scl_fall_in |-> !sde_out;
   endproperty

   a_RX_mealy_b_d_f: assert property(p_RX_mealy_b_d_f)
     else $error("i2c_fsm RX-mealy-b-d-f");

   property p_RX_mealy_b_d_e;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RX) && !stop_in && !scl_rise_in && scl_fall_in |-> sde_out;
   endproperty

   a_RX_mealy_b_d_e: assert property(p_RX_mealy_b_d_e)
     else $error("i2c_fsm RX-mealy-b-d-e");
   
   
   /////////////////////////////////////////////////////////////////////////////////////   
   // RACK
   /////////////////////////////////////////////////////////////////////////////////////

   // Transitions

   property p_RACK_a;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RACK) && stop_in |=> (state_r == IDLE);
   endproperty

   a_RACK_a: assert property(p_RACK_a)
     else $error("i2c_fsm RACK-a");

   property p_RACK_b_d;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RACK) && !stop_in && !scl_fall_in |=> (state_r == RACK);
   endproperty

   a_RACK_b_d: assert property(p_RACK_b_d)
     else $error("i2c_fsm RACK-b-d");

   property p_RACK_b_c_e;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RACK) && !stop_in && scl_fall_in && frameok_in |=> (state_r == IDLE);
   endproperty

   a_RACK_b_c_e: assert property(p_RACK_b_c_e)
     else $error("i2c_fsm RACK-b-c-e");

   property p_RACK_b_c_f;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RACK) && !stop_in && scl_fall_in && !frameok_in |=> (state_r == RX);
   endproperty

   a_RACK_b_c_f: assert property(p_RACK_b_c_f)
     else $error("i2c_fsm RACK-b-c-f");

   property p_RACK_default;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == RACK) && !(stop_in || scl_fall_in) |=> (state_r == RACK);
   endproperty

   a_RACK_default: assert property(p_RACK_default)
     else $error("i2c_fsm RACK-default");

   // Outputs

   property p_RACK_moore;
      @(posedge clk ) disable iff (rst_n == '0)
	(state_r == RACK) |-> (!ack_out && ul_out && !dl_out && byteen_out && clr_out && !next_out && oe_out && !osel_out && !sde_out );
   endproperty

   a_RACK_moore: assert property(p_RACK_moore)
     else $error("i2c_fsm RACK-moore");

   /////////////////////////////////////////////////////////////////////////////////////   
   // TX
   /////////////////////////////////////////////////////////////////////////////////////

   // Transitions

   property p_TX_a;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TX) && stop_in |=> (state_r == IDLE);
   endproperty

   a_TX_a: assert property(p_TX_a)
     else $error("i2c_fsm TX-a");

   property p_TX_b_c;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TX) && !stop_in && scl_rise_in |=> (state_r == TX);
   endproperty

   a_TX_b_c: assert property(p_TX_b_c)
     else $error("i2c_fsm TX-b-c");

   property p_TX_b_d_f;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TX) && !stop_in && !scl_rise_in && !scl_fall_in |=> (state_r == TX);
   endproperty

   a_TX_b_d_f: assert property(p_TX_b_d_f)
     else $error("i2c_fsm TX-b-d-f");

   property p_TX_b_d_e_h;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TX) && !stop_in && !scl_rise_in && scl_fall_in & !byteok_in |=> (state_r == TX);
   endproperty

   a_TX_b_d_e_h: assert property(p_TX_b_d_e_h)
     else $error("i2c_fsm TX-b-d-e-h");

   property p_TX_b_d_e_g;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TX) && !stop_in && !scl_rise_in && scl_fall_in & byteok_in |=> (state_r == TACK);
   endproperty

   a_TX_b_d_e_g: assert property(p_TX_b_d_e_g)
     else $error("i2c_fsm TX-b-d-e-g");

   property p_TX_default;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TX) && !(stop_in || (!scl_rise_in && scl_fall_in & byteok_in)) |=> (state_r == TX);
   endproperty

   a_TX_default: assert property(p_TX_default)
     else $error("i2c_fsm TX-default");

   // Outputs

   property p_TX_moore;
      @(posedge clk ) disable iff (rst_n == '0)
	(state_r == TX) |-> (!ack_out && !clr_out && !ul_out && dl_out && byteen_out && oe_out && osel_out  );
   endproperty

   a_TX_moore: assert property(p_TX_moore)
     else $error("i2c_fsm TX-moore");

   property p_TX_mealy_b_c;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TX) && !stop_in && scl_rise_in |-> next_out;
   endproperty

   a_TX_mealy_b_c: assert property(p_TX_mealy_b_c)
     else $error("i2c_fsm TX-mealy-b-c");

   property p_TX_mealy_b_d;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TX) && !stop_in && !scl_rise_in |-> !next_out;
   endproperty

   a_TX_mealy_b_d: assert property(p_TX_mealy_b_d)
     else $error("i2c_fsm TX-mealy-b-d");

   property p_TX_mealy_b_d_f;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TX) && !stop_in && !scl_rise_in && !scl_fall_in |-> !sde_out;
   endproperty

   a_TX_mealy_b_d_f: assert property(p_TX_mealy_b_d_f)
     else $error("i2c_fsm TX-mealy-b-d-f");

   property p_TX_mealy_b_d_e;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TX) && !stop_in && !scl_rise_in && scl_fall_in |-> sde_out;
   endproperty

   a_TX_mealy_b_d_e: assert property(p_TX_mealy_b_d_e)
     else $error("i2c_fsm TX-mealy-b-d-e");
   
   /////////////////////////////////////////////////////////////////////////////////////   
   // TACK
   /////////////////////////////////////////////////////////////////////////////////////

   // Transitions

   property p_TACK_a;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TACK) && stop_in |=> (state_r == IDLE);
   endproperty

   a_TACK_a: assert property(p_TACK_a)
     else $error("i2c_fsm TACK-a");

   property p_TACK_b_d;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TACK) && !stop_in && !scl_fall_in |=> (state_r == TACK);
   endproperty

   a_TACK_b_d: assert property(p_TACK_b_d)
     else $error("i2c_fsm TACK-b-d");

   property p_TACK_b_c_e;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TACK) && !stop_in && scl_fall_in && frameok_in |=> (state_r == IDLE);
   endproperty

   a_TACK_b_c_e: assert property(p_TACK_b_c_e)
     else $error("i2c_fsm TACK-b-c-e");

   property p_TACK_b_c_f;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TACK) && !stop_in && scl_fall_in && !frameok_in |=> (state_r == TX);
   endproperty

   a_TACK_b_c_f: assert property(p_TACK_b_c_f)
     else $error("i2c_fsm TACK-b-c-f");

   property p_TACK_default;
     @(posedge clk ) disable iff (rst_n == '0)
       (state_r == TACK) && !(stop_in || scl_fall_in) |=> (state_r == TACK);
   endproperty

   a_TACK_default: assert property(p_TACK_default)
     else $error("i2c_fsm TACK-default");

   // Outputs

   property p_TACK_moore;
      @(posedge clk ) disable iff (rst_n == '0)
	(state_r == TACK) |-> (!ack_out && !ul_out && dl_out && byteen_out && clr_out && !next_out && !osel_out && !sde_out );
   endproperty

   a_TACK_moore: assert property(p_TACK_moore)
     else $error("i2c_fsm TACK-moore");

   ///////////////////////////////////////////////////////////////////////////////////////
   // Covergroups
   ///////////////////////////////////////////////////////////////////////////////////////   
   
   covergroup cg_i2c_fsm_states @(posedge clk);
      coverpoint state_r;
   endgroup
   cg_i2c_fsm_states cg_i2c_fsm_states_inst = new;    
   
endmodule

`endif
