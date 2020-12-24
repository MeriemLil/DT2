`include "myfilter.svh"

import myfilter_pkg::*;

module i2c_slave
  
  (input logic  clk,
   input logic 	rst_n,
   inout tri 	scl_inout,
   inout tri 	sda_inout,
   
   output logic ul_out,
   output logic dl_out,   
   output logic sde_out,
   input logic 	sd_in,
   output logic sd_out
   );

   logic               sdaw;
   logic 	       scl;
   logic 	       sda;
   logic 	       past_scl;
   logic 	       past_sda;   
   logic 	       start;      
   logic 	       stop;
   logic 	       scl_rise;
   logic               scl_fal;
   logic	       frameok;
   logic               byteok;
   logic               addrok;
   logic               lastbit;
   logic               byteen;
   logic               oe;
   logic               osel;
   logic               ack;
   logic               next;
   logic               clr;

   assign sd_out = lastbit;
   assign sda_inout = sdaw;

   i2c_sync i2c_sync_1
     (
	.clk(clk),
        .rst_n(rst_n),
        .scl_in(scl_inout),
        .sda_in(sda_inout),
        .scl_out(scl),
        .sda_out(sda),      
        .past_scl_out(past_scl),
        .past_sda_out(past_sda)
      );
  
   i2c_detector i2c_detector_1
      (
       .clk(clk),
       .rst_n(rst_n),
       .scl_in(scl),
       .sda_in(sda),
       .past_scl_in(past_scl),
       .past_sda_in(past_sda),
       .start_out(start),
       .stop_out(stop),
       .scl_rise_out(scl_rise),
       .scl_fall_out(scl_fall)
      );

   i2c_fsm i2c_fsm_1
       (
       .clk(clk),
       .rst_n(rst_n),
       .start_in(start),
       .stop_in(stop),
       .scl_rise_in(scl_rise),
       .scl_fall_in(scl_fall),
       .frameok_in(frameok),
       .byteok_in(byteok),
       .addrok_in(addrok),
       .lastbit_in(lastbit),
       .sde_out(sde_out),
       .ul_out(ul_out),
       .dl_out(dl_out),
       .byteen_out(byteen),
       .oe_out(oe),
       .osel_out(osel),
       .ack_out(ack),
       .next_out(next),
       .clr_out(clr)
        );

   i2c_ctr i2c_ctr_1
       (
       .clk(clk),
       .rst_n(rst_n),
       .byteen_in(byteen),
       .clr_in(clr),
       .next_in(next),
       .frameok_out(frameok),
       .byteok_out(byteok)
        );

   i2c_srg i2c_srg_1
       (
      .clk(clk),
      .rst_n(rst_n),
      .clr_in(clr),
      .next_in(next),
      .bit_in(sda),
      .addrok_out(addrok),
      .bit_out(lastbit)	
	);

   i2c_omux i2c_omux_1
       (
      .clk(clk),
      .rst_n(rst_n),
      .sdaw_out(sdaw),
      .oe_in(oe),
      .osel_in(osel),
      .ack_in(ack),
      .sd_in(sd_in)
	);
endmodule


