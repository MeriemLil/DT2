`include "myfilter.svh"
import myfilter_pkg::*;

module i2c_ctr
  
  (input logic clk,
   input logic 	rst_n,
   input logic 	clr_in,
   input logic 	next_in,
   input logic 	byteen_in, 
   output logic byteok_out,
   output logic frameok_out   
   );

   logic [3:0] bitctr_r;
   logic [$clog2(I2C_FRAME_BYTES)-1:0] bytectr_r;
   logic seven;

   always_ff@(posedge clk or negedge rst_n)
     begin
	if (rst_n == '0)
	   bitctr_r <= '0;
        else 
	  begin
	     if (clr_in == '1)
 	   	bitctr_r <= '0;
             else if (next_in == '1 && bitctr_r < 8)
		bitctr_r <= bitctr_r + 1;
	     else if (next_in == '1 && bitctr_r >= 8)
 	   	bitctr_r <= '0;
	     else
	        bitctr_r <= bitctr_r;
          end
     end

   always_comb
     begin
        if (bitctr_r == 7)
	   seven = '1;
        else
	   seven = '0;

	if (bitctr_r == 8)
	   byteok_out = '1;
	else
	   byteok_out = '0; 
     end 


   always_ff@(posedge clk or negedge rst_n)
     begin
     	if (rst_n == '0)
           bytectr_r <= '0;
        else 
	   begin
	     if (byteen_in == '0)
		bytectr_r <= '0;
             else 
	      begin
		if (next_in == '1 && seven == '1 && bytectr_r < I2C_DATA_BYTES && clr_in == '0)
		   bytectr_r <= bytectr_r + 1;	
             	else if (next_in == '1 && seven == '1 && bytectr_r >= I2C_DATA_BYTES && clr_in == '0)
                   bytectr_r <= '0;
	        else 
		   bytectr_r <= bytectr_r;
              end 
	   end
     end

   always_comb
     begin
	if (bytectr_r == I2C_DATA_BYTES)
	   frameok_out = '1;
        else
           frameok_out = '0;
     end

   
endmodule

