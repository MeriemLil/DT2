create_clock -name clk -period 5.0 clk
set_input_delay -clock clk 0.0 rst_n
set_input_delay -clock clk 0.0 scl_inout
set_input_delay -clock clk 0.0 sda_inout
set_input_delay -clock clk 2.0 sd_in

set_output_delay -clock clk 2.0 ul_out
set_output_delay -clock clk 2.0 dl_out
set_output_delay -clock clk 2.0 sde_out
set_output_delay -clock clk 2.0 sd_out

