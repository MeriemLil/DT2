`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;

module filter_unit_svamod
  
  (input logic clk,
   input logic 		      rst_n,
   input logic 		      sde_in,
   input logic 		      sd_in, 
   input logic 		      sd_out, 
   input logic 		      ul_in,
   input logic 		      dl_in,   
   input logic [DATABITS-1:0] ext_in,
   input logic 		      extready_in,
   input logic [DATABITS-1:0] ext_out,
   input logic 		      extvalid_out,
   input logic 		      cmem_sd,
   input 		      dp_cmd_t dpc_cmd,
   input logic [DATABITS-1:0] cmem_d,
   input logic [DATABITS-1:0] dmem_d, 
   input logic [ACCBITS-1:0]  alu_d, 
   input logic [ACCBITS-1:0]  acc_d,
   input logic [DATABITS-1:0] acc_ext
   );

   
   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks (See myfilter.svh)
   ///////////////////////////////////////////////////////////////////////////////////////   

   `xcheck(sde_in);
   `xcheck(sd_in); 
   `xcheck(sd_out); 
   `xcheck(ul_in);
   `xcheck(dl_in);   
   `xcheck(ext_in);
   `xcheck(extready_in);
   `xcheck(ext_out);
   `xcheck(extvalid_out);
   `xcheck(cmem_sd);
   `xcheck(dpc_cmd);
   `xcheck(cmem_d);
   `xcheck(dmem_d); 
   `xcheck(alu_d); 
   `xcheck(acc_d);
   `xcheck(acc_ext);
   
endmodule // filter_unit_svamod


`endif
