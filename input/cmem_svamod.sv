`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;

module cmem_svamod
  (
   input logic 			      clk,
   input logic 			      rst_n,
   input logic 			      sde_in,
   input logic 			      sd_in,
   input logic 			      sd_out,
   input logic [$clog2(CMEMSIZE)-1:0] addr_in,
   input logic [DATABITS-1:0] 	      d_out,
   input logic [CMEMSIZE-1:0][DATABITS-1:0] mem_r
   );

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks (See myfilter.svh)
   ///////////////////////////////////////////////////////////////////////////////////////   

   `xcheck(sde_in);
   `xcheck(sd_in);
   `xcheck(sd_out);
   `xcheck(addr_in);
   `xcheck(d_out);
   `xcheck(mem_r);   

   property p_cmem_addr;
     @(posedge clk ) disable iff (rst_n == '0)
       addr_in < CMEMSIZE;
   endproperty

   m_cmem_addr: assume property(p_cmem_addr)
     else $error("cmem addr_in too big.");

   property p_stable_mem_r;
     @(posedge clk ) disable iff (rst_n == '0)
       !sde_in |=> mem_r == $past(mem_r);
   endproperty

   a_stable_mem_r: assert property(p_stable_mem_r)
     else $error("cmem variable mem_r not stable when !sde_in");

   property p_shift_mem_r;
      logic [$bits(mem_r)-1:0] pastmem;
      @(posedge clk ) disable iff (rst_n == '0)
       (sde_in, pastmem = mem_r) |=> mem_r == { pastmem[$bits(mem_r)-2:0], $past(sd_in) };
   endproperty

   a_shift_mem_r: assert property(p_shift_mem_r)
     else $error("cmem variable mem_r not shift when sde_in");
   
endmodule

`endif //  `ifndef SYNTHESIS
