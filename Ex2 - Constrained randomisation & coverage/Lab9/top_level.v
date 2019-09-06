//`include "alu.vhd"		//It is not possible to include a VHDL file inside a Verilog file
							//Instead, the command "vcom alu.vhd" should be included inside the file "run_check"
`include "alu_assertions.sv"
`include "fsm.v"

module top_level (  input tl_clock,
					input tl_reset,
					input tl_validi,
					input [31:0] tl_data_in,
					output logic tl_valido,
					output logic [31:0] tl_data_out
			);

        reg [31:0] prev_data_in;

        wire w_valido;
        wire [31:0] w_data_out;
        wire [31:0] w_AxB;
        wire [31:0] w_result;

        always_ff @(posedge tl_clock) begin
			if (tl_reset) begin
				prev_data_in <= 0;
			end
			else begin
				prev_data_in <= tl_data_in;		//To take the previous input value (A)
			end
        end

        ex2_1 fsm (
			.clk(tl_clock),
			.rst(tl_reset),
			.validi(tl_validi),
			.data_in(tl_data_in),
			.valido(w_valido),
			.data_out(w_data_out)
        );

        alu alu1 (
			.Clk(tl_clock),         //clock signal
			.A(prev_data_in),       //A (1 step previous input value in respect of alu1)
			.B(tl_data_in),         //B (current input value)
			.Op(3'b010),            //multiplication is configured to be done
			.R(w_AxB)               //output of ALU 1 (intermediate value)
        );
		
		//NOTE 1: Now the formula a*b+c (a=2 step back value, b=1 step back value, c=current value) is done by two ALUs units.
		//This operation is calculated in 2 steps: a*b (done by alu1) and ab+c (done by alu2). These operations are parallelized here as well.
		//This parallelization means the number of steps back is relative, so they depend on which ALU is working into. This is the reason why
		//input "tl_data_in" is used in both ALUs, as it would always be "b" for alu1 (current value at that specific time) and also "c" for
		//alu2 (current value at that specific time).

        alu alu2 (
			.Clk(tl_clock),         //clock signal
			.A(w_AxB),              //AxB value
			.B(tl_data_in),         //C (current input value)
			.Op(3'b000),            //addition is configured to be done
			.R(w_result)            //output of ALU 2 (final value)
        );

        assign tl_valido = w_valido;
        assign tl_data_out = w_result;		//The result from the 2 ALUs in series (lab9)
		//assign tl_data_out = w_data_out;	//The result from FSM (lab7)
		
		//NOTE 2: Because of ALUs have no reset, assertion nº1 (output 0 with reset high) cannot be passed, as it is not taken into account...

endmodule