`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;

module dmem_svamod
  (input logic clk,
   input logic 				    rst_n,
   input logic 				    sde_in,
   input logic 				    sd_in,
   input logic 				    sd_out,
   input 				    dmem_cmd_t cmd_in,
   input logic [$clog2(DMEMSIZE)-1:0] 	    addr_in,
   input logic [DATABITS-1:0] 		    d_in,
   input logic [DATABITS-1:0] 		    d_out,
   input logic [DMEMSIZE-1:0][DATABITS-1:0] mem_r
   );

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks (See myfilter.svh)
   ///////////////////////////////////////////////////////////////////////////////////////   

   `xcheck(sde_in);
   `xcheck(sd_in);
   `xcheck(sd_out);
   `xcheck(cmd_in);
   `xcheck(addr_in);
   `xcheck(d_in);
   `xcheck(d_out);
   `xcheck(mem_r);   

   property p_dmem_addr;
     @(posedge clk ) disable iff (rst_n == '0)
       addr_in < DMEMSIZE;
   endproperty

   m_dmem_addr: assume property(p_dmem_addr)
     else $error("dmem addr_in too big.");

   property p_stable_mem_r;
     @(posedge clk ) disable iff (rst_n == '0)
       !sde_in && (cmd_in == DMEM_READ) |=> mem_r == $past(mem_r);
   endproperty

   a_stable_mem_r: assert property(p_stable_mem_r)
     else $error("dmem variable mem_r not stable when !sde_in");

   property p_shift_mem_r;
      logic [$bits(mem_r)-1:0] 		    pastmem;
      @(posedge clk ) disable iff (rst_n == '0)
       (sde_in, pastmem = mem_r) |=> mem_r == { pastmem[$bits(mem_r)-2:0], $past(sd_in) };
   endproperty

   a_shift_mem_r: assert property(p_shift_mem_r)
     else $error("dmem variable mem_r not shift when sde_in");
     
endmodule


`endif
