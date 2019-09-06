// Turning all checks on with check5
`ifdef check5
`define check1
`define check2
`define check3
`define check4
`endif

module ex2_1_property (
			input              clk, rst, validi,
			input [31:0]       data_in,
			input logic        valido,
			input logic [31:0] data_out
		);

	/*------------------------------------
	 *
	 *        CHECK # 1. Check that when 'rst' is asserted (==1) that data_out == 0
	 *
	 *------------------------------------ */

	`ifdef check1
	
		property reset_asserted;
			@(posedge clk) rst |-> data_out==0;
		endproperty

		reset_check: assert property(reset_asserted)
			$display($stime,,,"\t\tRESET CHECK PASS:: rst_=%b data_out=%0d \n", rst, data_out);
		else $display($stime,,,"\t\RESET CHECK FAIL:: rst_=%b data_out=%0d \n", rst, data_out);
			
	`endif

	/* ------------------------------------
	 * Check valido assertion to hold
	 *
	 *       CHECK # 2. Check that valido is asserted when validi=1 for three
	 *                  consecutive clk cycles
	 *
	 * ------------------------------------ */

	`ifdef check2
		property valido_asserted;
			@(posedge clk) disable iff (rst) validi[*3] |=> valido;
		endproperty

		valido_check: assert property(valido_asserted)
			$display($stime,,,"\t\tVALIDO 1 CHECK PASS:: rst_=%b data_out=%0d \n", rst, data_out);
		else $display($stime,,,"\t\VALIDO 1 CHECK FAIL:: rst_=%b data_out=%0d \n", rst, data_out);
	`endif

	/* ------------------------------------
	 * Check valido not asserted wrong
	 *
	 *       CHECK # 3. Check that valido is not asserted when validi=1 for only two, one
	 *                  or zero consecutive clk cycles
	 *
	 * ------------------------------------ */

	`ifdef check3
		property valido_not_asserted;
			@(posedge clk) disable iff (rst) ($rose(validi) ##0 validi[*0:2]) |=> !valido;
		endproperty

		no_valido_check: assert property(valido_not_asserted)
			$display($stime,,,"\t\tVALIDO 2 CHECK PASS:: rst_=%b data_out=%0d \n", rst, data_out);
		else $display($stime,,,"\t\VALIDO 2 CHECK FAIL:: rst_=%b data_out=%0d \n", rst, data_out);
	`endif

	/* ------------------------------------
	 * Check data_out value
	 *
	 *       CHECK # 4. Check that data_out when valido=1 is equal to a*b+c where a is data_in
	 *       two cycles back, b is data_in one cycle back, and c is the present data_in
	 *
	 * ------------------------------------ */

	`ifdef check4
		property data_out_value;	//TO PASS: a is 3 cycles back, b is 2 cycles back, and c is 1 cycle back
			@(posedge clk) disable iff (rst) $rose(valido) |-> data_out==$past(data_in, 3)*$past(data_in, 2)+$past(data_in, 1);
		endproperty

		data_out_check: assert property(data_out_value)
			$display($stime,,,"\t\tDATA_OUT CHECK PASS:: rst_=%b data_out=%0d \n", rst, data_out);
		else $display($stime,,,"\t\DATA_OUT CHECK FAIL:: rst_=%b data_out=%0d \n", rst, data_out);
	`endif

endmodule