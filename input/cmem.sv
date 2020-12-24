`include "myfilter.svh"

import myfilter_pkg::*;

module cmem
  (input logic clk,
   input logic 			      rst_n,
   input logic 			      sde_in,
   input logic 			      sd_in,
   output logic 		      sd_out,
   input logic [$clog2(CMEMSIZE)-1:0] addr_in,
   output logic [DATABITS-1:0] 	      d_out
   );

   logic [CMEMSIZE-1:0][DATABITS-1:0] mem_r;
   logic [CMEMSIZE*DATABITS-1:0] mem_tmp;

   always_ff@(posedge clk or negedge rst_n)
      begin:mem_reg
	if (rst_n == '0)
	   begin
	     mem_r <= '0;
	     mem_tmp = '0;
	   end
	else
	   begin
	     if (sde_in == '1)
		begin
		  mem_tmp = mem_r;
		  mem_r <= {mem_tmp[$bits(mem_tmp)-2:0], sd_in};
		end
	   end
      end


   always_comb
      begin:read_mux
	d_out = mem_r[addr_in];
      end

   assign sd_out = mem_r[CMEMSIZE-1][DATABITS-1];
endmodule 

