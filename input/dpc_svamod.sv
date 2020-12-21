`include "myfilter.svh"

`ifndef SYNTHESIS

import myfilter_pkg::*;

module dpc_svamod
  (
   input logic clk, 
   input logic rst_n, 
   input logic ul_in,
   input logic dl_in,    
   input logic extready_in, 
   input       dp_cmd_t cmd_out,
   input       dpc_fsm_t state_r,
   input       dpc_fsm_t next_state   
   );

   ///////////////////////////////////////////////////////////////////////////////////////
   // X-Checks (See myfilter.svh)
   ///////////////////////////////////////////////////////////////////////////////////////   
   
   `xcheck(clk); 
   `xcheck(rst_n); 
   `xcheck(ul_in);
   `xcheck(dl_in);    
   `xcheck(extready_in); 
   `xcheck(cmd_out);
   `xcheck(state_r);
   `xcheck(next_state);

   ///////////////////////////////////////////////////////////////////////////////////////
   // Property Checks
   ///////////////////////////////////////////////////////////////////////////////////////   

   property p_extready_wait;
     @(posedge clk ) disable iff (rst_n == '0)
       !(!extready_in && cmd_out.dmem_cmd == DMEM_SHIFT);
   endproperty

   a_extready_wait: assert property(p_extready_wait)
     else $error("dpc: dmem SHIFT command issued when extready == '0");
   
endmodule



`endif
