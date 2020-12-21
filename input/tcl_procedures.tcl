proc alu_T6 { } {
    view -new wave -title "T6"
    add wave -noupdate /alu_tb/DUT_INSTANCE/cmd_in
    add wave -noupdate -radix decimal /alu_tb/DUT_INSTANCE/m1
    add wave -noupdate -radix decimal /alu_tb/DUT_INSTANCE/m2
    add wave -noupdate -radix decimal /alu_tb/DUT_INSTANCE/acc
    add wave -noupdate -radix decimal /alu_tb/DUT_INSTANCE/mul
    add wave -noupdate -radix decimal /alu_tb/DUT_INSTANCE/func
    add wave -noupdate -radix decimal /alu_tb/DUT_INSTANCE/sat
    wave zoom range [subTime $::Now {50 ns}]  $::Now
    configure wave -signalnamewidth 1
    configure wave -datasetprefix 0
}
