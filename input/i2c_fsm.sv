`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_fsm
  
  (input logic clk,
   input logic 	rst_n,
   input logic 	start_in,
   input logic 	stop_in,
   input logic 	scl_rise_in,
   input logic 	scl_fall_in,
   input logic 	addrok_in,
   input logic 	byteok_in,
   input logic 	frameok_in,
   input logic 	lastbit_in,
   output logic ul_out,
   output logic dl_out,
   output logic byteen_out,      
   output logic sde_out, 
   output logic clr_out, 
   output logic next_out,
   output logic oe_out,
   output logic osel_out,
   output logic ack_out
   );

   i2c_fsm_t state_r, next_state;   
   
   always_ff @(posedge clk or negedge rst_n)
     begin : state_reg
	if (rst_n == '0)
	  state_r <= IDLE;
	else
	  state_r <= next_state;
     end : state_reg

   // To do: Add combinational logic process
   
endmodule

