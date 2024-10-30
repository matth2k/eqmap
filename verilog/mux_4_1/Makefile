
SRCS=$(wildcard *.v)
FAMILY=xcup
SYNTH_OPT=-flatten -noclkbuf -noiopad
YOSYS=yosys # Yosys 0.33 (git sha1 2584903a060)
FSTEM=synth

.PHONY: all clean

all: mux_4_1_synth.v

clean:
	rm -f *_$(FSTEM).v *_$(FSTEM).ys

%_$(FSTEM).v: %_$(FSTEM).ys $(SRCS)
	+$(YOSYS) -s $<

%_$(FSTEM).ys: %.v
	@echo "read_verilog $(SRCS)" > $@
	@echo "synth_xilinx -top $* -family $(FAMILY) $(SYNTH_OPT)" >> $@
	@echo "write_verilog $*_$(FSTEM).v" >> $@
