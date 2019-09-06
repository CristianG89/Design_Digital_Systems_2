timeunit 10ns;
`include "alu_packet.sv"
`include "alu_assertions.sv"

module alu_tb();
	reg clk = 0;
	bit [7:0] a = 8'h0;
	bit [7:0] b = 8'h0;
	bit [2:0] op = 3'h0;
	wire [7:0] r;

	parameter NUMBERS = 10000;

	//make your vector here
	alu_data test_data[NUMBERS];
	
	//Make your loop here
	initial
	data_gen: begin
		#20			//Delay 20 cycles
		for (int i=0; i<NUMBERS; i++) begin
			test_data[i] = new;
			test_data[i].randomize();
			test_data[i].get_data(a, b, op);
			#20;	//Delay 20 cycles
		end
		$finish;
	end:data_gen
	
	//Displaying signals on the screen
	always @(posedge clk)
		$display($stime,,,"clk=%b a=%b b=%b op=%b r=%b",clk,a,b,op,r);

	//Clock generation
	always #10 clk=~clk;

	//Declaration of the VHDL alu
	alu dut (clk,a,b,op,r);

	//Make your opcode enumeration here
	enum {ADD, SUB, MULT, NOT, NAND, NOR, AND, OR} opcode;	//ADD=0, SUB=1, MULT=2, NOT=3, NAND=4, NOR=5, AND=6, OR=7

	//Make your covergroup here
	covergroup alu_cg @(posedge clk);		//Once instantiated, this covergroup will be executed in each positive edge of 'clk'
		OP : coverpoint opcode;
		A : coverpoint a {
			bins zero = { 0 };
			bins Small = { [1:50] };		//small and large in minor case are reserved words.
			bins hunds[3] = { [100:200] };	//We specify to cover this range in 3 bins so as to save memory ([100:133], [134:166], [167:200]).
			bins Large = { [200:$] };		//Each single value matched inside a range bin would count as covered bin.
			bins others[] = default;		//[] with no number inside means an independent bin for each value.
		}
		B : coverpoint b {
			bins zero = { 0 };
			bins Small = { [1:50] };
			bins hunds[3] = { [100:200] };
			bins Large = { [200:$] };
			bins others[] = default;
		}
		AB : cross A, B;
	endgroup

	//Initialize your covergroup here
	alu_cg cg_inst = new;

	//Sample covergroup here
	always @(posedge clk) begin
		cg_inst.sample();	//Statement to sample the whole covergroup (to be done always in each positive edge of 'clk')
    end						//NOTE: This block is an altervative to sample the covergroup that can be omitted,
							//as the covergroup itself already defines its sampling activation with positive edge of 'clk' (line 44)
endmodule :alu_tb
