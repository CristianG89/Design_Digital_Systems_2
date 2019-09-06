/* "assertions_hdlc" module is a test module containing the concurrent assertions.
   It is used by binding the signals of assertions_hdlc to the corresponding
   signals in the test_hdlc testbench. This is already done in bind_hdlc.sv
*/

module assertions_hdlc (
	output int   ErrCntConcAssertions,		//These I/O must match with the ones defined in the binding file (bind_hdlc)
	input  logic Clk,
	input  logic Rst,
	//Tx elements (1 real output + variables)
	input  logic Tx,
	input  logic Tx_ValidFrame,
	input  logic Tx_AbortedTrans,
	input  logic Tx_WriteFCS,			//NOTE: These I/O are not necessarily the final I/O from the main RTL file,
	input  logic Tx_InitZero,			//		but can be any real I/O and/or any internal variable, just whatever needed.
	input  logic Tx_StartFCS,
	input  logic Tx_RdBuff,
	input  logic Tx_NewByte,
	input  logic Tx_FCSDone,
	input  logic [7:0] Tx_Data,
	input  logic Tx_Done,
	input  logic Tx_Full,
	input  logic Tx_DataAvail,
	input  logic [7:0] Tx_FrameSize,
	input  logic [127:0][7:0] Tx_DataArray,
	input  logic [7:0] Tx_DataOutBuff,
	input  logic Tx_WrBuff,
	input  logic Tx_Enable,
	input  logic [7:0] Tx_DataInBuff,
	input  logic Tx_AbortFrame,
	//Rx elements (1 real input + variables)
	input  logic Rx,
	input  logic Rx_ValidFrame,
	input  logic Rx_WrBuff,
	input  logic Rx_EoF,
	input  logic Rx_AbortSignal,
	input  logic Rx_StartZeroDetect,
	input  logic Rx_FrameError,
	input  logic Rx_StartFCS,
	input  logic Rx_StopFCS,
	input  logic [7:0] Rx_Data,
	input  logic Rx_NewByte,
	input  logic Rx_FlagDetect,
	input  logic Rx_AbortDetect,
	input  logic RxD,
	input  logic Rx_FCSerr,
	input  logic Rx_Ready,
	input  logic [7:0] Rx_FrameSize,
	input  logic Rx_Overflow,
	input  logic [7:0] Rx_DataBuffOut,
	input  logic Rx_FCSen,
	input  logic Rx_RdBuff,
	input  logic Rx_Drop	
);

	initial begin
		ErrCntConcAssertions = 0;
	end

	/****************************************************************
	* Assertion 1 - Correct data in RX buffer according to RX input *
	****************************************************************/
	// Immediate assertion...
	
	/**********************************************************************************************************************
	* Assertion 2 - Attempting to read RX buffer after aborted frame, frame error or dropped frame should result in zeros *
	**********************************************************************************************************************/
	// Immediate assertion...
	
	/*************************************************************************************
	* Assertion 3 - Correct bits set in RX status/control register after receiving frame *
	*************************************************************************************/
	// Immediate assertion...
	
	/*****************************************************************
	* Assertion 4 - Correct TX output according to written TX buffer *
	*****************************************************************/
	// Immediate assertion...
	
	/***********************************************************************************
	* Assertion 5 - Start/end frame pattern generation (Start and end flag: 0111_1110) *
	***********************************************************************************/
	sequence Rx_Flag_Sec;	//A frame should start and end with flag sequence "0111 1110"
		Rx==0 ##1 Rx==1[*6] ##1 Rx==0;		//NOTE: Least significant bit is sent first
	endsequence

	property RX_FlagDetect_Pr;	//Check if flag sequence is generated and detected
		Rx_Flag_Sec |=> ##1 Rx_FlagDetect;	//FlagDetect is only high after 2 clock cycles (2 FFs are used after Rx input)
	endproperty

	RX_FlagDetect_Assert: assert property (@(posedge Clk) disable iff (!Rst) RX_FlagDetect_Pr) begin
		$display("PASS conc 5: Start/End flag seen and detected");
	end else begin 
		$display("FAIL conc 5: Start/End flag seen but NOT detected");
		ErrCntConcAssertions++;
	end

	/**********************************************************************************
	* Assertion 6 - Zero insertion (Tx) and removal (Rx) for transparent transmission *
	**********************************************************************************/
	sequence Tx_Num127_Sec;		//Specific sequence for number 127 in Tx (including one extra bit to 0 because of zero insertion)
		!Tx and $past(Tx) and $past(Tx,2) and $past(!Tx,3) and $past(Tx,4) and $past(Tx,5) and $past(Tx,6) and $past(Tx,7) and $past(Tx,8);
	endsequence

	property Tx_ZeroInsertion_Pr;	//Tx output sends out the bits that Tx_Data held 26 clock cycles ago.
		Tx_ValidFrame and Tx_Num127_Sec |-> $past(Tx_Data, 26)==8'b01111111;	//The value to check must be 127 (01111111)
	endproperty

	sequence Rx_Num127_Sec;		//Specific sequence for number 127 in Rx (including one extra bit to 0 because of zero insertion)
		!Rx and $past(Rx) and $past(Rx,2) and $past(!Rx,3) and $past(Rx,4) and $past(Rx,5) and $past(Rx,6) and $past(Rx,7) and $past(Rx,8);
	endsequence

	property Rx_ZeroRemoval_Pr;		//Rx_Data holds the bits that Rx input received 11 clock cycles before.
		Tx_ValidFrame and Rx_Num127_Sec |-> ##11 Rx_Data==8'b01111111;	//The value to check must be 127 (01111111)
	endproperty

	Tx_ZeroInsertion_Assert: assert property (@(posedge Clk) disable iff (!Rst) Tx_ZeroInsertion_Pr) begin
		$display("PASS conc 6: Tx Zero inserted and detected");
	end else begin
		$display("FAIL conc 6: Tx Zero inserted but NOT detected");
		ErrCntConcAssertions++;
	end

	Rx_ZeroRemoval_Assert: assert property (@(posedge Clk) disable iff (!Rst) Rx_ZeroRemoval_Pr) begin
		$display("PASS conc 6: Rx Zero inserted and detected");
	end else begin
		$display("FAIL conc 6: Rx Zero inserted but NOT detected");
		ErrCntConcAssertions++;
	end
	
	/************************************************************************************
	* Assertion 7 - Idle pattern generation and checking (1111_1111 when not operating) *
	************************************************************************************/
	sequence Tx_Idle_pattern_Sec;	//If no data is being sent, the output should be just "1111_1111"
		Tx[*8];		//Though Tx sends data to Rx bitwise, the other blocks handle data as bytes, so Idle means at least one byte is 1
	endsequence
	
	property Tx_Idle_pattern_Pr;	//Unless something is being sent, FrameSize is always 0!
		!Tx_ValidFrame and Tx_FrameSize=='0 |-> Tx_Idle_pattern_Sec;
	endproperty

	Tx_Idle_pattern_Assert: assert property (@(posedge Clk) disable iff (!Rst) Tx_Idle_pattern_Pr) begin
		//$display("PASS conc 7: Tx only sends 1 in IDLE state");	//Commented out because it appears many times...
	end else begin
		$display("FAIL conc 7: Tx sends 0 in IDLE state");
		ErrCntConcAssertions++;
	end
	
	/******************************************************************
	* Assertion 8 - Abort pattern generation and checking (1111_1110) *
	******************************************************************/
	sequence Rx_Abort_Sec;	//To terminate a frame, an abort pattern "1111_1110" is generated
		!Rx ##1 Rx[*7];		//NOTE: Least significant bit is sent first
	endsequence
	
	property RX_AbortFlag_Pr;	//Check if abort flag sequence is generated and detected
		Rx_Abort_Sec |=> ##1 Rx_AbortDetect;	//Rx_AbortDetect is only high after 2 clock cycles (2 FFs are used after Rx input)
	endproperty
	
	RX_AbortFlag_Assert: assert property (@(posedge Clk) disable iff (!Rst) RX_AbortFlag_Pr) begin
		$display("PASS conc 8: Abort flag seen and detected");
	end else begin
		$display("FAIL conc 8: Abort flag seen but NOT detected");
		ErrCntConcAssertions++;
	end
	
	/********************************************************************************************
	* Assertion 9 - When aborting frame during transmission, Tx_AbortedTrans should be asserted *
	********************************************************************************************/	
	property Tx_Abort_pattern_Pr;
		$fell(Tx_AbortFrame) |=> $rose(Tx_AbortedTrans);
	endproperty

	Tx_Abort_pattern_Assert: assert property (@(posedge Clk) disable iff (!Rst) Tx_Abort_pattern_Pr) begin
		$display("PASS conc 9: Transmission aborted after frame abort");
	end else begin
		$display("FAIL conc 9: Transmission NOT aborted after frame abort");
		ErrCntConcAssertions++;
	end
	
	/******************************************************************************************
	* Assertion 10 - Abort pattern detected during valid frame should generate Rx_AbortSignal *
	******************************************************************************************/
	property RX_AbortSignal_Pr;		//If abort asserted and deasserted during valid frame, then abort signal should go high
		Rx_ValidFrame and $fell(Rx_AbortDetect) |-> $rose(Rx_AbortSignal);
	endproperty		//Rx_AbortSignal and Rx_AbortDetect have overlapping relation because they are set in different blocks

	RX_AbortSignal_Assert: assert property (@(posedge Clk) disable iff (!Rst) RX_AbortSignal_Pr) begin
		$display("PASS conc 10: AbortSignal asserted after AbortDetect during ValidFrame");
	end else begin
		$display("FAIL conc 10: AbortSignal NOT asserted after AbortDetect during ValidFrame");
		ErrCntConcAssertions++;
	end
	
	/*********************************************
	* Assertion 11 - CRC generation and Checking *
	*********************************************/
	// Immediate assertion...
	
	/*********************************************************************************************
	* Assertion 12 - When a whole RX frame has been received, check if end of frame is generated *
	*********************************************************************************************/	
	property Rx_EoF_Pr;		//End of Frame is asserted once end flag sequence has been detected
		$fell(Rx_ValidFrame) and !Rx_AbortSignal |=> $rose(Rx_EoF);
	endproperty
	
	Rx_EoF_Assert: assert property (@(posedge Clk) disable iff (!Rst) Rx_EoF_Pr) begin
		$display("PASS conc 12: End of frame asserted after receiving ValidFrame");
	end else begin
		$display("FAIL conc 12: End of frame NOT asserted after receiving ValidFrame");
		ErrCntConcAssertions++;
	end
	
	/************************************************************************************
	* Assertion 13 - When receiving more than 128 bytes, Rx_Overflow should be asserted *
	************************************************************************************/	
	property Rx_Overflow_Pr;	//In case of Overflow, frame size will be fixed to 126
		Rx_FrameSize==8'd126 and $past(Rx_EoF) and $past(Rx_Ready) |-> $past(Rx_Overflow);
	endproperty			//Max 126 bytes = 128 bytes in buffer - 2 FCS bytes)

	Rx_Overflow_Assert: assert property (@(posedge Clk) disable iff (!Rst) Rx_Overflow_Pr) begin
		$display("PASS conc 13: Overflow asserted after 128 bytes received");
	end else begin
		$display("FAIL conc 13: Overflow NOT asserted after 128 bytes received");
		ErrCntConcAssertions++;
	end
	
	/*************************************************************************************************************
	* Assertion 14 - Rx_FrameSize should equal number of bytes received in frame (max. 126 [128 buffer - 2 FCS]) *
	*************************************************************************************************************/	
	// Immediate assertion...
	
	/***********************************************************************************
	* Assertion 15 - Rx_Ready should indicate byte(s) in RX buffer is ready to be read *
	***********************************************************************************/	
	property Rx_Ready_Pr;	//Rx_Ready is only asserted once Rx frame completely finished and without errors
		!Rx_Drop and !Rx_FrameError and !Rx_AbortSignal and $rose(Rx_EoF) |-> $rose(Rx_Ready);
	endproperty

	Rx_Ready_Assert: assert property (@(posedge Clk) disable iff (!Rst) Rx_Ready_Pr) begin
		$display("PASS conc 15: Rx_Ready asserted with Rx_EoF and no errors");
	end else begin
		$display("FAIL conc 15: Rx_Ready NOT asserted with Rx_EoF and no errors");
		ErrCntConcAssertions++;
	end
	
	/*********************************************************************************************
	* Assertion 16 - Non-byte aligned data or error in FCS checking should result in frame error *
	*********************************************************************************************/
	property Rx_FrameError_Pr;		//$rose(Rx_FlagDetect) and !Rx_NewByte = Non-byte aligned
		Rx_ValidFrame and (($rose(Rx_FlagDetect) and !Rx_NewByte) or $rose(Rx_FCSerr)) |=> ##1 Rx_FrameError;
	endproperty

	Rx_FrameError_Assert: assert property (@(posedge Clk) disable iff (!Rst) Rx_FrameError_Pr) begin
		$display("PASS conc 16: Rx_FrameError asserted with either non-byte aligned or Rx_FCSerr");
	end else begin
		$display("FAIL conc 16: Rx_FrameError NOT asserted with neither non-byte aligned nor Rx_FCSerr");
		ErrCntConcAssertions++;
	end
	
	/*************************************************************************************************
	* Assertion 17 - Tx_Done should be asserted when entire TX buffer has been read for transmission *
	*************************************************************************************************/
	property Tx_Done_Pr;		//Tx_DataAvail=1 means data still available in Tx buffer
		Tx_ValidFrame and $fell(Tx_DataAvail) |-> $rose($past(Tx_Done));
	endproperty

	Tx_Done_Assert: assert property (@(posedge Clk) disable iff (!Rst) Tx_Done_Pr) begin
		$display("PASS conc 17: Tx_Done asserted after frame sent");
	end else begin
		$display("FAIL conc 17: Tx_Done NOT asserted after frame sent");
		ErrCntConcAssertions++;
	end
	
	/****************************************************************************************************
	* Assertion 18 - Tx_Full should be asserted after writing 126 or more bytes (overflow) to TX buffer *
	****************************************************************************************************/
	// Immediate assertion...
	
endmodule

/*General notes about concurrent assertions not applied here (just discarded possible solutions):
	- For defining a value range within '[]', symbols '=' and '*' can be used as 'non consecutive' and 'consecutive' respectively ([=126] or [*126]).
	- Inside properties, variables can be defined ONLY as local, in order to work with them. Example: int counter = 0;
	- Each I/O used in both antecedent and consequent can be associated with an operation.
			Example: ($rose(Rx_NewByte), counter++) |=> (Rx_FrameSize, $display(counter));
*/