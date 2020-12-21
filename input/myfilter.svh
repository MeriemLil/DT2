`ifndef __myfilter_svh__
`define __myfilter_svh__

//timeunit 1ns;
//timeprecision 1ps;

`define INCLUDE_ASSERTIONS

`define xcheck(name) X_``name``: assert property ( @(posedge clk) disable iff (rst_n !== '1) !$isunknown( name ))

		
`endif

