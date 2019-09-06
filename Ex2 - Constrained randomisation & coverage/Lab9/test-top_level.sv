module test_top_level;
	logic tb_clock;
	logic tb_reset;
	logic tb_validi;
	logic [31:0] tb_data_in;
	wire		 tb_valido;
	wire [31:0]  tb_data_out;


	top_level dut (				//To instantiate module inside the testbench, connection direction is: ".module(testbench)"
		.tl_clock(tb_clock),
		.tl_reset(tb_reset),
		.tl_validi(tb_validi),
		.tl_data_in(tb_data_in),
		.tl_valido(tb_valido),
		.tl_data_out(tb_data_out)
	);

	//Property (assertion) file is binded here
	bind top_level top_level_property top_level_bind (	//To bind the properties, connections direction is: ".properties(module)"
		.pr_clock(tl_clock),
		.pr_reset(tl_reset),
		.pr_validi(tl_validi),
		.pr_data_in(tl_data_in),
		.pr_valido(tl_valido),
		.pr_data_out(tl_data_out)
	);

	initial begin
		tb_clock=1'b0;
		set_stim;       //Function/Task is called (as C/C++)
		@(posedge tb_clock);
		$finish(2);
	end

	always @(posedge tb_clock)
			$display($stime,,,"tb_reset=%b tb_clock=%b tb_validi=%b DIN=%0d tb_valido=%b DOUT=%0d",
					tb_reset, tb_clock, tb_validi, tb_data_in, tb_valido, tb_data_out);

	always #5 tb_clock=!tb_clock;

	task set_stim;          //Function declaration
		tb_reset=1'b0; tb_validi=0'b1; tb_data_in=32'b1;
		@(negedge tb_clock) tb_reset=1;
		@(negedge tb_clock) tb_reset=0;

		@(negedge tb_clock); tb_validi=1'b0; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b0; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b0; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b0; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b0; tb_data_in+=32'b1;    //tb_clock = 145

		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b0; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b0; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b0; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b1; tb_data_in+=32'b1;
		@(negedge tb_clock); tb_validi=1'b0; tb_data_in+=32'b1;

		@(negedge tb_clock);
	endtask

endmodule