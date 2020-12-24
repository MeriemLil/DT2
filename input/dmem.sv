`include "myfilter.svh"
import myfilter_pkg::*;

module dmem
  (input logic clk,
   input logic 			      rst_n,
   input logic 			      sde_in,
   input logic 			      sd_in,
   output logic 		      sd_out,
   input 			      dmem_cmd_t cmd_in,
   input logic [$clog2(DMEMSIZE)-1:0] addr_in,
   input logic [DATABITS-1:0] 	      d_in,
   input logic [DATABITS-1:0] 	      ext_in,   
   output logic [DATABITS-1:0] 	      d_out
   );

  logic [DMEMSIZE-1:0][DATABITS-1:0] mem_r;
  logic [DMEMSIZE*DATABITS-1:0] mem_tmp;

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
	     else if (cmd_in == DMEM_SHIFT)
		begin
		  for(int i = 1; i < DMEMSIZE; i = i + 1)
		     mem_r[i] <= mem_r[i - 1];
		  mem_r[0] <= ext_in;
		end
	     else if (cmd_in == DMEM_WRITE)
		mem_r[addr_in] <= d_in;
	     else if (cmd_in == DMEM_CLEAR)
		mem_r <= '0;
	   end
      end


   always_comb
      begin:read_mux
	d_out = mem_r[addr_in];
      end

   assign sd_out = mem_r[DMEMSIZE-1][DATABITS-1];



endmodule 

