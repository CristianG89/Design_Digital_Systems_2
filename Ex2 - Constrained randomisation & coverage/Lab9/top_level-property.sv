// Turning all checks on with check5
`ifdef check5
	`define check1
	`define check2
	`define check3
	`define check4
`endif

module top_level_property (
			input pr_clock,
			input pr_reset,
			input pr_validi,
			input [31:0] pr_data_in,
			input logic pr_valido,
			input logic [31:0] pr_data_out
		);

	/*------------------------------------
	 *
	 *        CHECK # 1. Check that when 'pr_reset' is asserted (==1) that pr_data_out == 0
	 *
	 *------------------------------------ */

	`ifdef check1
		property reset_asserted;
			@(posedge pr_clock) pr_reset |-> pr_data_out==0;
		endproperty

		reset_check: assert property(reset_asserted)
			$display($stime,,,"\t\tRESET CHECK PASS:: reset_=%b pr_data_out=%0d \n", pr_reset, pr_data_out);
		else $display($stime,,,"\t\pr_reset CHECK FAIL:: reset_=%b pr_data_out=%0d \n", pr_reset, pr_data_out);
	`endif

	/* ------------------------------------
	 * Check pr_valido assertion to hold
	 *
	 *       CHECK # 2. Check that pr_valido is asserted when pr_validi=1 for three
	 *                  consecutive pr_clock cycles
	 *
	 * ------------------------------------ */

	`ifdef check2
		property valid_out_asserted;
			@(posedge pr_clock) disable iff (pr_reset) pr_validi[*3] |=> pr_valido;
		endproperty

		valid_out_check: assert property(valid_out_asserted)
			$display($stime,,,"\t\tvalid_out 1 CHECK PASS:: reset_=%b pr_data_out=%0d \n", pr_reset, pr_data_out);
		else $display($stime,,,"\t\pr_valido 1 CHECK FAIL:: reset_=%b pr_data_out=%0d \n", pr_reset, pr_data_out);
	`endif

	/* ------------------------------------
	 * Check pr_valido not asserted wrong
	 *
	 *       CHECK # 3. Check that pr_valido is not asserted when pr_validi=1 for only two, one
	 *                  or zero consecutive pr_clock cycles
	 *
	 * ------------------------------------ */

	`ifdef check3
		property valid_out_not_asserted;
			@(posedge pr_clock) disable iff (pr_reset) ($rose(pr_validi) ##0 pr_validi[*0:2]) |=> !pr_valido;
		endproperty

		no_valid_out_check: assert property(valid_out_not_asserted)
			$display($stime,,,"\t\tvalid_out 2 CHECK PASS:: reset_=%b pr_data_out=%0d \n", pr_reset, pr_data_out);
		else $display($stime,,,"\t\pr_valido 2 CHECK FAIL:: reset_=%b pr_data_out=%0d \n", pr_reset, pr_data_out);
	`endif

	/* ------------------------------------
	 * Check pr_data_out value
	 *
	 *       CHECK # 4. Check that pr_data_out when pr_valido=1 is equal to a*b+c where a is pr_data_in
	 *       two cycles back, b is pr_data_in one cycle back, and c is the present pr_data_in
	 *
	 * ------------------------------------ */

	`ifdef check4
		property data_out_value;        //TO PASS: a is 3 cycles back, b is 2 cycles back, and c is 1 cycle back
			@(posedge pr_clock) disable iff (pr_reset) $rose(pr_valido) |-> pr_data_out==$past(pr_data_in, 3)*$past(pr_data_in, 2)+$past(pr_data_in, 1);
		endproperty

		data_out_check: assert property(data_out_value)
			$display($stime,,,"\t\tDATA_OUT CHECK PASS:: reset_=%b pr_data_out=%0d \n", pr_reset, pr_data_out);
		else $display($stime,,,"\t\pr_data_out CHECK FAIL:: reset_=%b pr_data_out=%0d \n", pr_reset, pr_data_out);
	`endif

endmodule