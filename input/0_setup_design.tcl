####################################################################################################
# Top module selection
####################################################################################################

set DESIGN_NAME "myfilter"
#set DESIGN_NAME "i2c_slave"
#set DESIGN_NAME "filter_unit"
#set DESIGN_NAME "reset_sync"
set DESIGN_NAME "i2c_detector"
#set DESIGN_NAME "i2c_omux"
#set DESIGN_NAME "i2c_sync"
#set DESIGN_NAME "i2c_srg"
#set DESIGN_NAME "i2c_ctr"
#set DESIGN_NAME "i2c_fsm"
#set DESIGN_NAME "cmem"
#set DESIGN_NAME "dmem"
#set DESIGN_NAME "acc"
#set DESIGN_NAME "alu"
#set DESIGN_NAME "dpc"

####################################################################################################
# Design Parameters
####################################################################################################

set NTAPS                 5       ; # Define your filter's tap count
set CLOCK_PERIOD          7       ; # Clock period in ns.

####################################################################################################
# Settings for all tools
####################################################################################################

set CLOCK_NAMES          { "clk" }
set CLOCK_PERIODS        {  5.0 }
set RESET_NAMES          { "rst_n" }
set RESET_LEVELS         {   0  }
set RESET_STYLES         { "async" }
set RTL_LANGUAGE         "SystemVerilog"

set SHOW_REPORTS 0 ;                # 1= EDA tool opens reports after script has ended

source "input/tcl_procedures.tcl" ; # Misc. stuff

####################################################################################################
# RTL Verification
####################################################################################################

set RTL_SIMULATION_TIME "-all"                       ; # "-all" (run to $finisg) all time+unit, e.g. 1ms"
set VSIM_SCHEMATIC      1                            ; # 1: QuestaSim generates schematic (can be slow)
set SVA_BIND_FILE       "input/myfilter_svabind.svh" ; # Assertion module bindings
set QUESTA_INIT_FILE    "input/clock.questa_init"    ; # Initialization file for Questa tools
set QFORMAL_COVERAGE    1                            ; # Enable/disable formal coverage in Questa PropertyCheck

####################################################################################################
# Logic Synthesis
####################################################################################################

set SDC_FILE            "input/clock.sdc"
set DC_SUPPRESS_MESSAGES { "UID-401" "TEST-130" "TIM-104" "VER-26" "TIM-179" }
set DC_WRITE_PARASITICS  1

####################################################################################################
# Gate-Level Simulation
####################################################################################################

set GATELEVEL_SIMULATION_TIME "-all"
set VSIM_GATELEVEL_OPTIONS    "+nowarn3448 +nowarn3438 +nowarn8756 -suppress 3009 -debugdb"
set VSIM_GATELEVEL_WAVES      "input/5_vsim_module_gatelevel_waves.tcl"
set VSIM_GATELEVEL_LOG        1
set GATELEVEL_SDF             MAX
set POSTLAYOUT_SDF            MAX

####################################################################################################
# Top-module-specific settings
####################################################################################################

switch $DESIGN_NAME {

    "myfilter" {
	set DESIGN_FILES { \
			       "input/myfilter_pkg.sv" \
			       "input/i2c_pkg.sv" \
			       "input/i2c_sync.sv" \
			       "input/i2c_detector.sv" \
			       "input/i2c_ctr.sv" \
			       "input/i2c_srg.sv" \
			       "input/i2c_fsm.sv" \	
	                       "input/i2c_omux.sv" \		       
	                       "input/i2c_slave.sv" \
			       "input/i2c_sync_svamod.sv" \
			       "input/i2c_detector_svamod.sv" \
			       "input/i2c_ctr_svamod.sv" \
			       "input/i2c_srg_svamod.sv" \
			       "input/i2c_fsm_svamod.sv" \	
	                       "input/i2c_omux_svamod.sv" \		       
	                       "input/i2c_slave_svamod.sv" \
			       "input/cmem.sv" \
			       "input/dmem.sv" \			       
			       "input/alu.sv" \
			       "input/acc.sv" \
			       "input/dpc.sv" \
			       "input/filter_unit.sv" \			       
			       "input/cmem_svamod.sv" \
			       "input/dmem_svamod.sv" \			       
			       "input/alu_svamod.sv" \
			       "input/acc_svamod.sv" \
			       "input/dpc_svamod.sv" \
			       "input/filter_unit_svamod.sv" \
			       "input/reset_sync.sv" \
			       "input/myfilter.sv" \
			       "input/myfilter_svamod.sv" \			       
			   }
	set TESTBENCH_FILES { \
				  "input/i2c_if.sv" \
				  "input/myfilter_tb.sv" \
				  "input/myfilter_test.sv" \
			      }
	set SDC_FILE input/myfilter.sdc
	set QUESTA_INIT_FILE input/myfilter.questa_init
#       set VSIM_DISABLE_TIMINGCHECKS { "*sff1*" }
	set SYNTHESIS_DONT_UNGROUP { "reset_sync" "i2c_slave" "filter_unit"  }
	set SYNTHESIS_FIX_HOLD 1
	set SYNTHESIS_RECREM_ARCS 1
    }

    "i2c_slave" {
	set DESIGN_FILES { \
			       "input/myfilter_pkg.sv" \
			       "input/i2c_sync.sv" \
			       "input/i2c_detector.sv" \
			       "input/i2c_ctr.sv" \
			       "input/i2c_srg.sv" \
			       "input/i2c_fsm.sv" \	
	                       "input/i2c_omux.sv" \		       
	                       "input/i2c_slave.sv" \
			       "input/i2c_sync_svamod.sv" \
			       "input/i2c_detector_svamod.sv" \
			       "input/i2c_ctr_svamod.sv" \
			       "input/i2c_srg_svamod.sv" \
			       "input/i2c_fsm_svamod.sv" \	
	                       "input/i2c_omux_svamod.sv" \		       
	                       "input/i2c_slave_svamod.sv" \
			   }
	set TESTBENCH_FILES { \
				  "input/i2c_if.sv" \
				  "input/i2c_slave_test.sv" \
				  "input/i2c_slave_tb.sv" \
			      }
	set SDC_FILE input/i2c_slave.sdc
	set QUESTA_INIT_FILE input/i2c_slave.questa_init
	set GATELEVEL_SIMULATION_CONFIGURATION "input/i2c_slave_gatelevel_cfg.sv"
	set VSIM_DISABLE_TIMINGCHECKS { "*sff1*" }
	set SYNTHESIS_DONT_UNGROUP { "i2c_sync" "i2c_detector" "i2c_srg" "i2c_ctr" "i2c_omux" "i2c_fsm" }
    }
    
    "filter_unit" {
	set DESIGN_FILES { \
			       "input/myfilter_pkg.sv" \
			       "input/cmem.sv" \
			       "input/dmem.sv" \			       
			       "input/alu.sv" \
			       "input/acc.sv" \
			       "input/dpc.sv" \
			       "input/filter_unit.sv" \
			       "input/cmem_svamod.sv" \
			       "input/dmem_svamod.sv" \			       
			       "input/alu_svamod.sv" \
			       "input/acc_svamod.sv" \
			       "input/dpc_svamod.sv" \
			       "input/filter_unit_svamod.sv" \
			   }
	set TESTBENCH_FILES { \
				  "input/filter_unit_tb.sv" \
				  "input/filter_unit_test.sv" \
			      }
    }
    
    "reset_sync" {
	set DESIGN_FILES { \
			       "input/myfilter_pkg.sv" \
			       "input/reset_sync.sv" \
			   }
	set TESTBENCH_FILES { \
				  "input/reset_sync_tb.sv" \
			      }
	set SDC_FILE input/clock.sdc
	set QUESTA_INIT_FILE input/clock.questa_init
	set RTL_SIMULATION_TIME 200ns
	set GATELEVEL_SIMULATION_TIME 200ns
#       set VSIM_DISABLE_TIMINGCHECKS { "*sff1*" "*sff2*" }
    }

    default {
	set DESIGN_FILES  [list "input/myfilter_pkg.sv" "input/${DESIGN_NAME}_svamod.sv" "input/${DESIGN_NAME}.sv" ]
	set TESTBENCH_FILES  [list "input/i2c_pkg.sv" "input/${DESIGN_NAME}_tb.sv" "input/${DESIGN_NAME}_test.sv"  ]
    }
}





