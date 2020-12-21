`ifndef __i2c_assumes_svh__
`define __i2c_assumes_svh__ 1

// This value is used in assumes to prevent formal verification form creating
// two fast I2C waveforms

localparam int Clock_per_SCL = 4;


sequence s_i2c_start;
   (scl_inout && sda_inout) ##1 $fell(sda_inout) && scl_inout;
endsequence   

sequence s_i2c_cycle;
   (scl_inout) [* Clock_per_SCL:$] ##1 !scl_inout [* 1:$] ##1 $rose(scl_inout);
endsequence   

sequence s_i2c_stop;
   (scl_inout && !sda_inout) [* Clock_per_SCL:$] ##1 (scl_inout && $rose(sda_inout));
endsequence   

property p_i2c_waveform;
   @(posedge clk)
     s_i2c_start |=> s_i2c_cycle [* 1:$] ##1 s_i2c_stop;
endproperty

m_i2c_waveform: assume property(p_i2c_waveform) else $error("I2C waveform error");

property p_scl_waveform;
   @(posedge clk)
     !$stable(scl_inout) |=> $stable(scl_inout) [* Clock_per_SCL];
endproperty

m_scl_waveform: assume property(p_scl_waveform) else $error("I2C SCL waveform error");   

`endif
