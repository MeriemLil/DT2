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

   always_comb
     begin
	ul_out = '0;
   	dl_out = '0;
  	byteen_out = '0;  
   	sde_out = '0;
   	clr_out = '0;
   	next_out = '0;
   	oe_out = '0;
   	osel_out = '0;
   	ack_out = '0;

	case (state_r)
	   IDLE:
	     begin
		clr_out = '1;
		if (start_in == '1)
		   next_state = HRX;
		else
		   next_state = IDLE;
	      end

	   HRX:
	      begin
		if (stop_in == '1)
		   next_state = IDLE;
		else 
		   if (scl_rise_in == '1)
		     begin
		        next_out = '1;
		        next_state = HRX;
		     end
		   else 
		     begin
			next_out = '0;
			if (byteok_in && scl_fall_in)
			   next_state = HACK;
			else
			   next_state = HRX;
		     end
	      end

	   HACK:
	     begin
		if (stop_in == '1)
		   next_state = IDLE;
		else
		   begin
		     if (addrok_in == '1)
			begin
			  ack_out = '0;
			  oe_out = '1;
			  if (scl_fall_in == '1)
			     begin
				clr_out = '1;
				if (lastbit_in == '1)
				   next_state = TX;
				else
				   next_state = RX;
			     end
			  else
			      begin
				clr_out = '0;
				next_state = HACK;
			      end
			 end
		      else
			begin
			   ack_out = '1;
			   oe_out = '0;
			   clr_out = '0;
			   if (scl_fall_in == '1)
			      next_state = IDLE;
			   else
			      next_state = HACK;
			end
                   end
	     end

	   TX:
	     begin
	        dl_out = '1;
		byteen_out = '1;
		osel_out = '1;
		oe_out = '1;

		if (stop_in == '1)
		   next_state = IDLE;
		else
		   begin
		     if (scl_rise_in == '1)
			begin
 			   next_out = '1;
			   next_state = TX;
			end
		     else
			begin
			   next_out = '0;
			   if (scl_fall_in == '1)
			      begin
				sde_out = '1;
				if (byteok_in == '1)
				   next_state = TACK;
				else
				   next_state = TX;
			      end
			   else
			      begin
				sde_out = '0;
				next_state = TX;
			      end
			end

		   end
	     end

	   TACK:
	     begin
		dl_out = '1;
		byteen_out = '1;
		clr_out = 1;
		if (stop_in == '1)
		   next_state = IDLE;
		else
		   begin
		     if (scl_fall_in == '1)
			begin
			   if (frameok_in == '1)
			      next_state = IDLE;
			   else
			      next_state = TX;
			end
		     else
			next_state = TACK;
		   end
	     end

	   RX:
	     begin
		ul_out = '1;
		byteen_out = '1;
		if (stop_in == '1)
		   next_state = IDLE;
		else
		   begin
		      if (scl_rise_in == '1)
			begin
			   next_out = '1;
			   next_state = RX;
			end 
		      else
			begin
			   next_out = '0;
			   if (scl_fall_in == '1)
			      begin
				sde_out = '1;
				if (byteok_in == '1)
				   next_state = RACK;
				else
				   next_state = RX;
			      end
			   else
			      begin
				sde_out = '0;
				next_state = RX;
			      end
			end
		   end
	     end

	   RACK:
	     begin
		ul_out = '1;
		byteen_out = '1;
		oe_out = '1;
		clr_out = '1;
		
		if (stop_in == '1)
		   next_state = IDLE;
		else
		   begin
		      if (scl_fall_in == '1)
			begin
			   if (frameok_in == '1)
			      next_state = IDLE;
			   else
			      next_state = RX;
			end
		      else
			next_state = RACK;
		   end
	     end

	endcase

     end

   
endmodule

