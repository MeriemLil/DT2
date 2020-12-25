`include "myfilter.svh"
import myfilter_pkg::*;

module filter_unit
  
  (input logic clk,
   input logic 		       rst_n,
   input logic 		       sde_in,
   input logic 		       sd_in, 
   output logic 	       sd_out, 
   input logic 		       ul_in,
   input logic 		       dl_in,   
   input logic [DATABITS-1:0]  ext_in,
   input logic 		       extready_in,
   output logic [DATABITS-1:0] ext_out,
   output logic 	       extvalid_out
   );

   dp_cmd_t dpc_cmd;
   logic cmem_sd;
   logic [DATABITS-1:0] cmem_d;
   logic [DATABITS-1:0] dmem_d;
   logic [ACCBITS-1:0] alu_d;
   logic [DATABITS-1:0] acc_ext;
   logic [ACCBITS-1:0] acc_d;

   

   dpc dpc_1
       (
	.clk(clk),
        .rst_n(rst_n),
	.ul_in(ul_in),
	.dl_in(dl_in),
	.extready_in(extready_in),
	.cmd_out(dpc_cmd)
	);
   
   cmem cmem_1
        (
	.clk(clk),
        .rst_n(rst_n),
	.sde_in(sde_in),
	.sd_in(sd_in),
	.addr_in(dpc_cmd.cmem_addr),
	.sd_out(cmem_sd),
	.d_out(cmem_d)
	);

   dmem dmem_1
	(
	.clk(clk),
        .rst_n(rst_n),
	.sde_in(sde_in),
	.sd_in(cmem_sd),
	.cmd_in(dpc_cmd.dmem_cmd),
	.addr_in(dpc_cmd.dmem_addr),
	.d_in(acc_ext),
	.ext_in(ext_in),
	.sd_out(sd_out),
	.d_out(dmem_d)
	);

   alu alu_1 
	(
	.clk(clk),
        .rst_n(rst_n),
	.cmd_in(dpc_cmd.alu_cmd),
	.m1_in(cmem_d),
	.m2_in(dmem_d),
	.acc_in(acc_d),
	.d_out(alu_d)
	);

   acc acc_1
	(
	.clk(clk),
        .rst_n(rst_n),
	.cmd_in(dpc_cmd.acc_cmd),
	.d_in(alu_d),
	.ext_out(acc_ext),
	.d_out(acc_d)
	);

   assign extvalid_out = dpc_cmd.extvalid;
   assign ext_out = acc_ext;
endmodule


   


