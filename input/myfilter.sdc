create_clock -name clk -period 7.0 clk

set_input_delay -clock clk 0.0 rst_n
set_input_delay -clock clk 0.0 scl_inout
set_input_delay -clock clk 0.0 sda_inout
set_input_delay -clock clk 1.4 ext_in
set_input_delay -clock clk 1.4 extready_in

set_output_delay -clock clk 1.4 ext_out
set_output_delay -clock clk 1.4 extvalid_out



