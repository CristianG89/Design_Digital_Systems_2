module test_ex2_1;
	logic clk, rst, validi;
	logic [31:0] data_in;
	wire         valido;
	wire [31:0]  data_out;

	ex2_1 dut (
		clk, rst, validi,
		data_in,
		valido,
		data_out
	);

	//Property (assertion) file is binded here
	bind ex2_1 ex2_1_property ex2_1_bind (
		clk, rst, validi,
		data_in,
		valido,
		data_out
	);

	initial begin
		clk=1'b0;
		set_stim;	//Function/Task is called (as C/C++)
		@(posedge clk);
		$finish(2);
	end

	always @(posedge clk)
		$display($stime,,,"rst=%b clk=%b validi=%b DIN=%0d valido=%b DOUT=%0d",
			rst, clk, validi, data_in, valido, data_out);

	always #5 clk=!clk;

	task set_stim;		//Function declaration
		rst=1'b0; validi=0'b1; data_in=32'b1;
		@(negedge clk) rst=1;
		@(negedge clk) rst=0;

		@(negedge clk); validi=1'b0; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b0; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b0; data_in+=32'b1;
		@(negedge clk); validi=1'b0; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b0; data_in+=32'b1;	//clk = 145

		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b0; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b0; data_in+=32'b1;
		@(negedge clk); validi=1'b0; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b1; data_in+=32'b1;
		@(negedge clk); validi=1'b0; data_in+=32'b1;

		@(negedge clk);
	endtask

endmodule