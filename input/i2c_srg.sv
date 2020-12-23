`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_srg
  
  (input logic clk,
   input logic 	     rst_n,
   input logic 	     clr_in,
   input logic 	     next_in,
   input logic 	     bit_in,
   output logic      bit_out,
   output logic      addrok_out
   );

   logic [7:0] srg_r;

   always_ff@(posedge clk or negedge rst_n)
     begin
	if (rst_n == '0)
	  srg_r <= '0;
	else if (clr_in == '1)
	  srg_r <= '0;
	else
	  begin
 	    if (next_in == '1)
	      begin
		srg_r[0] <= bit_in;
		for (int i = 0; i < 7; i = i + 1)
		    srg_r[i+1] <= srg_r[i];
	      end
	  end 
     end


    always_comb
      begin
  	if (srg_r[7:1] == I2C_ADDRESS)
	   addrok_out = '1;
	else 
	   addrok_out = '0; 
      end

   assign bit_out = srg_r[0];
  
endmodule


