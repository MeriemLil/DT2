create_clock -name clk -period 5.0 clk

set_input_delay -clock clk 0.0 rst_n
set_input_delay -clock clk 0.0 scl_inout
set_input_delay -clock clk 0.0 sda_inout
set_input_delay -clock clk 2.0 ext_in
set_input_delay -clock clk 2.0 extready_in

set_output_delay -clock clk 2.0 ext_out
set_output_delay -clock clk 2.0 extvalid_out



