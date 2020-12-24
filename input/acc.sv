`include "myfilter.svh"
import myfilter_pkg::*;

module acc
  (input logic clk,
   input logic 		       rst_n,
   input 		       acc_cmd_t cmd_in,
   input logic [ACCBITS-1:0]   d_in,
   output logic [ACCBITS-1:0]  d_out,
   output logic [DATABITS-1:0] ext_out
   );

   logic [ACCBITS-1:0] acc_r;

   always_ff@(posedge clk or negedge rst_n)
      begin: acc_reg
	if (rst_n == '0)
	   acc_r <= '0;
	else
	   begin
	     if (cmd_in == ACC_NOP)
		acc_r <= acc_r;
	     else if (cmd_in == ACC_LOAD)
		acc_r <= d_in;
	     else if (cmd_in == ACC_CLEAR)
		acc_r <= '0;
	   end
      end

   assign ext_out = acc_r[DATABITS-1:0];
   assign d_out = acc_r;
   
endmodule


