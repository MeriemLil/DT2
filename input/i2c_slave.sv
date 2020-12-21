`include "myfilter.svh"

import myfilter_pkg::*;

module i2c_slave
  
  (input logic clk,
   input logic 	rst_n,
   inout tri 	scl_inout,
   inout tri 	sda_inout,
   
   output logic ul_out,
   output logic dl_out,   
   output logic sde_out,
   input logic 	sd_in,
   output logic sd_out
   );

   
endmodule


