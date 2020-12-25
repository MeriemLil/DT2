`include "myfilter.svh"
import myfilter_pkg::*;

module dpc
  
  (input logic clk,
   input logic rst_n,
   input logic ul_in,
   input logic dl_in, 
   input logic extready_in, 
   output      dp_cmd_t cmd_out );


   dpc_fsm_t state_r, next_state;

	
   always_comb
   begin
   next_state = STOPPED;
   cmd_out = CMD_NOP;

   case(state_r)
      STOPPED:
	begin
	  cmd_out = CMD_NOP;
	  if (ul_in == '0)
	     next_state = STOPPED;
	  else
	     next_state = PROGRAM;
	end

      PROGRAM:
	begin
	  cmd_out = CMD_NOP;
	  if (dl_in == '1)
	     next_state = STOPPED;
	  else if (ul_in == '1)
	     next_state = PROGRAM;
	  else
	     next_state = EXTIN;
	end

      EXTIN:
	begin
	  cmd_out = CMD_SHIFT;
	  if (dl_in == '1 || ul_in == '1)
	     next_state = STOPPED;
	  else
	    begin
	      if (extready_in != '1)
		begin
	         cmd_out = CMD_NOP;
	 	 next_state = EXTIN;
		end
	      else
	         next_state = TAP0;
	    end
	   end


      TAP0:
	begin
	  cmd_out = CMD_TAP0F;
	  if (dl_in == '1 || ul_in == '1)
	     next_state = STOPPED;
	  else
	     next_state = TAP1;
	end

      TAP1:
	begin
	  cmd_out = CMD_TAP1;
	  if (dl_in == '1 || ul_in == '1)
	     next_state = STOPPED;
	  else
	     next_state = TAP2;
	end

      TAP2:
	begin
	  cmd_out = CMD_TAP2;
	  if (dl_in == '1 || ul_in == '1)
	     next_state = STOPPED;
	  else
	     next_state = TAP3;
	end

      TAP3:
	begin
	  cmd_out = CMD_TAP3;
	  if (dl_in == '1 || ul_in == '1)
	     next_state = STOPPED;
	  else
	     next_state = TAP4;
	end

      TAP4:
	begin
	  cmd_out = CMD_TAP4;
	  if (dl_in == '1 || ul_in == '1)
	     next_state = STOPPED;
	  else
	     next_state = SAT;
	end

      SAT:
	begin
	  cmd_out = CMD_SAT_SH;
	  if (dl_in == '1 || ul_in == '1)
	     next_state = STOPPED;
	  else
	     next_state = EXTOUT;
	end

      EXTOUT:
	begin
	  cmd_out = CMD_TAP0;
	  next_state = PROGRAM;
	end
   endcase;
   end

   always_ff @(posedge clk or negedge rst_n)
     begin 
	if (rst_n == '0)
	  state_r <= STOPPED;
	else
	  state_r <= next_state;
     end
endmodule


