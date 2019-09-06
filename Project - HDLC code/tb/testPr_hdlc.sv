// testPr_hdlc contains the testbench of the system (so simulation) as well as the immediate assertions

//"program" defines a testbench (SV introduces this statement for testbench, instead of "module", with small differences...)
program testPr_hdlc (in_hdlc uin_hdlc);	//"uin_hdlc" is an instantiation of the interface "in_hdlc"
	int ErrCntImmAssertions;			//To show all immediate assertion errors
	parameter TxSC_Addr		= 3'b000;	//Address of register TxSC
	parameter TxBuff_Addr	= 3'b001;	//Address of register TxBuff
	parameter RxSC_Addr		= 3'b010;	//Address of register RxSC
	parameter RxBuff_Addr	= 3'b011;	//Address of register RxBuff
	parameter RxLen_Addr	= 3'b100;	//Address of register RxLen
	
	parameter Tx_AbortFrame = 8'h04;	//Inside register TxSC, bit "Tx_AbortFrame"
	parameter Tx_Enable		= 8'h02;	//Inside register TxSC, bit "Tx_Enable"
	parameter Tx_Done		= 8'h01;	//Inside register TxSC, bit "Tx_Done"
	parameter Rx_FCSen		= 8'h20;	//Inside register RxSC, bit "Rx_FCSen"
	parameter Rx_Drop		= 8'h02;	//Inside register RxSC, bit "Rx_Drop"

	covergroup Tx_CoverGroup @(posedge uin_hdlc.Clk);	//One covergroup for Tx module, to be executed (once has been initialized)
		Tx: coverpoint uin_hdlc.Tx {					//in every positive edge of 'clk'
			bins No_Tx = {0};
			bins Tx = {1};
		}
		Tx_ValidFrame: coverpoint uin_hdlc.Tx_ValidFrame {	//Inside covergroup, there are defined as many coverpoints (input/output/variable)
			bins No_Tx_ValidFrame = {0};					//as desired (only a bunch of them could be used, just the interesting/used ones).
			bins Tx_ValidFrame = {1};
		}
		Tx_AbortedTrans: coverpoint uin_hdlc.Tx_AbortedTrans {
			bins No_Tx_AbortedTrans = {0};
			bins Tx_AbortedTrans = {1};
		}
		Tx_RdBuff: coverpoint uin_hdlc.Tx_RdBuff {	//Inside coverpoint, there are as many bins (specific values or value range to cover)
			bins No_Tx_RdBuff = {0};				//as desired. To ensure a bin is covered, its defined value (or at least one
			bins Tx_RdBuff = {1};					//value within defined range) should be inserted into the variable (coverpoint).		
		}
		Tx_Done: coverpoint uin_hdlc.Tx_Done {
			bins No_Tx_Done = {0};
			bins Tx_Done = {1};
		} 
		Tx_Full: coverpoint uin_hdlc.Tx_Full {
			bins No_Tx_Full = {0};
			bins Tx_Full = {1};
		}
		Tx_DataAvail: coverpoint uin_hdlc.Tx_DataAvail {
			bins No_Tx_DataAvail = {0};
			bins Tx_DataAvail = {1};
		}
		Tx_FrameSize: coverpoint uin_hdlc.Tx_FrameSize {
			bins Tx_FrameSize_Zero = {0};
			bins Tx_FrameSize_Valid = {[1:125]};	//As no "[]" have been defined in the bin name, there is only one for the whole range [1:125]
			bins Tx_FrameSize_Overflow = {126};		//(which means just one single value within this range inserted is enough to cover the bin).
		}
		Tx_DataOutBuff: coverpoint uin_hdlc.Tx_DataOutBuff {
			bins Tx_DataOutBuff_Zero = {0};
			bins Tx_DataOutBuff_Valid = {[1:255]};
		}
		Tx_Enable: coverpoint uin_hdlc.Tx_Enable {
			bins No_Tx_Enable = {0};
			bins Tx_Enable = {1};
		}
		Tx_AbortFrame: coverpoint uin_hdlc.Tx_AbortFrame {
			bins No_Tx_AbortFrame = {0};
			bins Tx_AbortFrame = {1};
		}
	endgroup
		
	covergroup Rx_CoverGroup @(posedge uin_hdlc.Clk);	//One covergroup for Rx module, to be executed (once has been initialized)
		Rx: coverpoint uin_hdlc.Rx {					//in every positive edge of 'clk'
			bins No_Rx = {0};
			bins Rx = {1};
		}
		Rx_ValidFrame: coverpoint uin_hdlc.Rx_ValidFrame {
			bins No_Rx_ValidFrame = {0};
			bins Rx_ValidFrame = {1};
		}
		Rx_EoF: coverpoint uin_hdlc.Rx_EoF {
			bins No_Rx_EoF = {0};
			bins Rx_EoF = {1};
		}
		Rx_AbortSignal: coverpoint uin_hdlc.Rx_AbortSignal {
			bins No_Rx_AbortSignal = {0};
			bins Rx_AbortSignal = {1};
		}
		Rx_FrameError: coverpoint uin_hdlc.Rx_FrameError {
			bins No_Rx_FrameError = {0};
			bins Rx_FrameError = {1};
		}
		Rx_FlagDetect: coverpoint uin_hdlc.Rx_FlagDetect {
			bins No_Rx_FlagDetect = {0};
			bins Rx_FlagDetect = {1};
		}
		Rx_AbortDetect: coverpoint uin_hdlc.Rx_AbortDetect {
			bins No_Rx_AbortDetect = {0};
			bins Rx_AbortDetect = {1};
		}
		RxD: coverpoint uin_hdlc.RxD {
			bins No_RxD = {0};
			bins RxD = {1};
		}
		Rx_FCSerr: coverpoint uin_hdlc.Rx_FCSerr {
			bins No_Rx_FCSerr = {0};
			bins Rx_FCSerr = {1};
		}
		Rx_Ready: coverpoint uin_hdlc.Rx_Ready {
			bins No_Rx_Ready = {0};
			bins Rx_Ready = {1};
		}
		Rx_FrameSize: coverpoint uin_hdlc.Rx_FrameSize {
			bins Rx_FrameSize_Zero = {0};
			bins Rx_FrameSize_Valid = {[1:125]};
			bins Rx_FrameSize_Overflow = {126};
		}
		Rx_Overflow: coverpoint uin_hdlc.Rx_Overflow {
			bins No_Rx_Overflow = {0};
			bins Rx_Overflow = {1};
		}
		Rx_FCSen: coverpoint uin_hdlc.Rx_FCSen {
			bins No_Rx_FCSen = {0};
			bins Rx_FCSen = {1};
		}
		Rx_Drop: coverpoint uin_hdlc.Rx_Drop {
			bins No_Rx_Drop = {0};
			bins Rx_Drop = {1};
		}
	endgroup
	
	Tx_CoverGroup Tx_Object;	//Tx functional coverage object instantiation
	Rx_CoverGroup Rx_Object;	//Rx functional coverage object instantiation
	
	//"initial" and "final" statements have the simulation code (testbench)
	initial begin		//Code inside "initial" statement is executed once at the beginning of testbench
		$display("*************************************************************");
		$display("%t - Starting Test Program", $time);
		$display("*************************************************************");

		TB_Init();			//Testbench initialization
		Tx_Object = new();	//Tx functional coverage initialization
		Rx_Object = new();	//Rx functional coverage initialization

		$display("*************** ASSERTION 1 ***************");
		TB_Assertion1();
		TB_Reset();
		$display("*******************************************");
		
		$display("*************** ASSERTION 2 ***************");
		TB_Assertion2();
		TB_Reset();
		$display("*******************************************");
		
		$display("************* ASSERTIONS 3, 13 ************");
		TB_Assertion3_13();
		TB_Reset();
		$display("*******************************************");
		
		$display("*************** ASSERTION 4 ***************");
		TB_Assertion4();
		TB_Reset();
		$display("*******************************************");
		
		$display("********* ASSERTIONS 5, 12, 14, 15 ********");
		TB_Assertion5_12_14_15();
		TB_Reset();
		$display("*******************************************");
		
		$display("*************** ASSERTION 6 ***************");
		TB_Assertion6();
		TB_Reset();
		$display("*******************************************");
		
		$display("*************** ASSERTION 7 ***************");
		TB_Assertion7();
		TB_Reset();
		$display("*******************************************");
		
		$display("************* ASSERTIONS 8, 10 ************");
		TB_Assertion8_10();
		TB_Reset();
		$display("*******************************************");
		
		$display("*************** ASSERTION 9 ***************");
		TB_Assertion9();
		TB_Reset();
		$display("*******************************************");

		$display("*************** ASSERTION 11 **************");
		TB_Assertion11();
		TB_Reset();
		$display("*******************************************");
		
		$display("*************** ASSERTION 16 **************");
		TB_Assertion16();
		TB_Reset();
		$display("*******************************************");
		
		$display("*************** ASSERTION 17 **************");
		TB_Assertion17();
		TB_Reset();
		$display("*******************************************");
		
		$display("*************** ASSERTION 18 **************");
		TB_Assertion18();
		TB_Reset();
		$display("*******************************************");
		
		$display("*************************************************************");
		$display("%t - Finishing Test Program", $time);
		$display("*************************************************************");
		$stop;		//To finish the simulation (so "final" statement will be finally executed)
	end

	final begin			//Code inside "final" is executed once the testbench stops/finishes
		$display("*****************************************");
		$display("* \tImmediate Assertion Errors: %0d\t  *", ErrCntImmAssertions);
		$display("* \tConcurrent Assertion Errors: %0d\t  *", uin_hdlc.ErrCntConcAssertions);
		$display("*****************************************");
	end
	
	task TB_Init();		//All inputs from "hdlc" module are fixed to stand-by value (defined inside "initial begin" statement)
		uin_hdlc.Clk         =   1'b0;
		uin_hdlc.Rst         =   1'b0;
		uin_hdlc.Address     = 3'b000;
		uin_hdlc.WriteEnable =   1'b0;
		uin_hdlc.ReadEnable  =   1'b0;
		uin_hdlc.DataIn      =     '0;
		uin_hdlc.TxEN        =   1'b1;
		uin_hdlc.Rx          =   1'b1;
		uin_hdlc.RxEN        =   1'b1;

		ErrCntImmAssertions	 = 		0;
		#1000ns;
		uin_hdlc.Rst         =   1'b1;
	endtask

	task TB_Reset();	//Function to restart the whole system
		uin_hdlc.Rst = 1'b0;
		#1000ns;
		uin_hdlc.Rst = 1'b1;
		#1000ns;
	endtask
	
	task WriteAddress(input logic [2:0] Address, input logic [7:0] Data);	//Function to write the Registers Interface
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Address     = Address;
		uin_hdlc.WriteEnable = 1'b1;
		uin_hdlc.DataIn      = Data;
		@(posedge uin_hdlc.Clk);
		uin_hdlc.WriteEnable = 1'b0;
	endtask

	task ReadAddress(input logic [2:0] Address, output logic [7:0] Data);	//Function to read the Registers Interface
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Address	= Address;
		uin_hdlc.ReadEnable	= 1'b1;
		#100ns;
		Data				= uin_hdlc.DataOut;
		@(posedge uin_hdlc.Clk);
		uin_hdlc.ReadEnable = 1'b0;
	endtask
	
	task HDLC_genFlag(int FlagType);	//Inserts "Flag" field (of HDLC frame) into Rx input (either start/end or abort sequence)
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b0;				//It starts with the least significant bit
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b1;
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b1;				
		@(posedge uin_hdlc.Clk);		//NOTE: Before writing into a physical input, wait for positive edge of clock
		uin_hdlc.Rx = 1'b1;				//(in the same way, do not put the wait statement if no input will be written),
		@(posedge uin_hdlc.Clk);		//otherwise the values will NOT be synchronized.
		uin_hdlc.Rx = 1'b1;
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b1;
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b1;
		@(posedge uin_hdlc.Clk);
		if(FlagType)					//Start/end and abort sequences are only different in the most significant bit.
			uin_hdlc.Rx = 1'b1;			//abort sequence 	 = 1111_1110
		else							//start/end sequence = 0111_1110
			uin_hdlc.Rx = 1'b0;
	endtask
	
	task HDLC_genAddr();				//Inserts "Address" field (of HDLC frame) into Rx input
		for (int i=0; i<8; i++) begin	//Random value generated ("Address" field does not need to be any specific value)
			@(posedge uin_hdlc.Clk);		//NOTE: To avoid confusions with concurrent assertions, it is important not to
			uin_hdlc.Rx = ~uin_hdlc.Rx;		//put more than five 1s together and to finish with 0.
		end
	endtask
	
	task HDLC_genControl();				//Inserts "Control" field (of HDLC frame) into Rx input
		for (int i=0; i<8; i++) begin	//Random value generated ("Control" field does not need to be any specific value)
			@(posedge uin_hdlc.Clk);
			if (i%2 == 0)					//NOTE: To avoid confusions with concurrent assertions, it is important not to
				uin_hdlc.Rx = ~uin_hdlc.Rx;	//put more than five 1s together and to finish with 0.
		end
	endtask
	
	task HDLC_genInfo(int InfoSize, output logic[129:0][7:0] InfoData);	//Generates "Information" field of HDLC frame
		for (int i=0; i<InfoSize; i++) begin	//Random value (Information field does not need to be any specific value)
			InfoData[i] = $urandom;				//$urandom = unsigned random number
		end
	endtask
	
	task HDLC_genFCS(int InfoSize, input logic[129:0][7:0] InfoData, output logic[1:0][7:0] FCS_Data);	//Generates "FCS" field of HDLC frame
		logic [23:0] CheckReg;			//It performs CRC algorithm to Information field data to generate FCS (16) bits		
		CheckReg[15:8] = InfoData[1];
		CheckReg[7:0] = InfoData[0];
		for(int i=2; i<InfoSize; i++) begin
			CheckReg[23:16] = InfoData[i];
			for(int j=0; j<8; j++) begin
				if(CheckReg[0]) begin
					CheckReg[0]    = CheckReg[0] ^ 1;
					CheckReg[1]    = CheckReg[1] ^ 1;
					CheckReg[13:2] = CheckReg[13:2];
					CheckReg[14]   = CheckReg[14] ^ 1;
					CheckReg[15]   = CheckReg[15];
					CheckReg[16]   = CheckReg[16] ^ 1;
				end
				CheckReg = CheckReg >> 1;
			end
		end
		FCS_Data[1] = CheckReg[15:8];
		FCS_Data[0] = CheckReg[7:0];
	endtask
	
	task MakeRxStimulus(int Size, int Length, input logic [129:0][7:0] HDLC_byte);	//Writes requested data into Rx input (stimulate the system)
		logic [4:0] PrevData;					//5 bits array (for zero detection)
		PrevData = '0;
		for (int i=0; i<Size; i++) begin
			//(Length==8) HDLC_byte[i][Length] = 1'b0;	//Correction to ensure MSb is 0 (only applies if length 8, but matrix is 9 bits)
			for (int j=0; j<Length; j++) begin
				if(&PrevData) begin				//If the current 5 bits in a row are all 1 (AND bitwise),
					@(posedge uin_hdlc.Clk);	//an extra 0 is added after them.
					uin_hdlc.Rx = 1'b0;			//(this 0 insertion only applies to "Information" and "FCS" fields!)
					PrevData = PrevData >> 1;
					PrevData[4] = 1'b0;
				end
				@(posedge uin_hdlc.Clk);		//Requested data is sent to Rx
				uin_hdlc.Rx = HDLC_byte[i][j];
				PrevData = PrevData >> 1;
				PrevData[4] = HDLC_byte[i][j];
			end
		end
	endtask
	
	task waitClock(int clockCycles);	//Delay in a hardware system (by waiting for clock cycles)
		repeat(clockCycles)
			@(posedge uin_hdlc.Clk);
	endtask
	
	task TB_Assertion1();
		logic [7:0] RxBuff_Data;
		logic [29:0][7:0] HDLC_Data;
		logic  [1:0][7:0] FCS_Data;

		HDLC_genFlag(0);        //One complete frame is sent
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(HDLC_Data), HDLC_Data);
		MakeRxStimulus($size(HDLC_Data), $size(HDLC_Data[0]), HDLC_Data);
		HDLC_genFCS($size(HDLC_Data), HDLC_Data, FCS_Data);
		MakeRxStimulus($size(FCS_Data), $size(FCS_Data[0]), FCS_Data);
		HDLC_genFlag(0);

		@(posedge uin_hdlc.Rx_Ready);			//Wait for Rx_Ready to know when RX buffer is ready to be read.
		ReadAddress(RxBuff_Addr, RxBuff_Data);	//Rx_Buff is read twice two discard the first two values
		ReadAddress(RxBuff_Addr, RxBuff_Data);	//(from "Address" and "Control" fields).
		
		for(int i=0; i<$size(HDLC_Data); i++) begin	//Every received byte is checked to be the right one.
			ReadAddress(RxBuff_Addr, RxBuff_Data);	//The following values from Rx_Buff are only from "Information" field.
			assert (RxBuff_Data==HDLC_Data[i])		//The value from register should match the previous put into Rx input (random).
				$display("PASS imm 1: Rx input value matches with register Rx_Buff");
			else begin
				$display("FAIL imm 1: Rx input value does NOT match with register Rx_Buff");
				ErrCntImmAssertions++;
			end
		end
		
		waitClock(50);		//50 clock cycles to ensure all data is processed.
	endtask

	task TB_Assertion2();
		logic [7:0] RxBuff_Data;
		logic [5:0][7:0] HDLC_Data;
		logic [5:0][8:0] Data_FrameError;	//One extra bit to generate FrameError
		logic [1:0][7:0] FCS_Data;
		
		//Aborted frame case generated
		HDLC_genFlag(0);
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(HDLC_Data), HDLC_Data);
		MakeRxStimulus($size(HDLC_Data), $size(HDLC_Data[0]), HDLC_Data);
		HDLC_genFlag(1);	//Abort flag generate (before current HDLC frame is finished)
		
		@(negedge uin_hdlc.Rx_AbortDetect);		//Wait until the Abort signal is really detected
		ReadAddress(RxBuff_Addr, RxBuff_Data);	//The last (unique) received byte is taken from register Rx_Buff
		assert (RxBuff_Data == '0)
			$display("PASS imm 2: Aborted frame case - Rx_Buff is 0");
		else begin
			$display("FAIL imm 2: Aborted frame case - Rx_Buff is NOT 0");
			ErrCntImmAssertions++;
		end
		
		waitClock(50);		//50 clock cycles to ensure all data is processed.
		
		//FrameError case generated
		HDLC_genFlag(0);
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(Data_FrameError), Data_FrameError);
		MakeRxStimulus($size(Data_FrameError), $size(Data_FrameError[0]), Data_FrameError);
		//The whole frame must have extra bits to activate FrameError (so nothing else sent, as module consider FCS the last 2 bytes before flag)
		HDLC_genFlag(0);
		
		@(posedge uin_hdlc.Rx_FrameError);		//Wait until the Frame Error is really detected
		ReadAddress(RxBuff_Addr, RxBuff_Data);	//The last (unique) received byte is taken from register Rx_Buff
		assert (RxBuff_Data == '0)
			$display("PASS imm 2: Frame error case - Rx_Buff is 0");
		else begin
			$display("FAIL imm 2: Frame error case - Rx_Buff is NOT 0");
			ErrCntImmAssertions++;
		end
		
		waitClock(50);		//50 clock cycles to ensure all data is processed.
		
		//Rx_Drop case generated
		HDLC_genFlag(0);
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(HDLC_Data), HDLC_Data);
		MakeRxStimulus($size(HDLC_Data), $size(HDLC_Data[0]), HDLC_Data);
		HDLC_genFCS($size(HDLC_Data), HDLC_Data, FCS_Data);
		MakeRxStimulus($size(FCS_Data), $size(FCS_Data[0]), FCS_Data);
		HDLC_genFlag(0);
		
		WriteAddress(RxSC_Addr, Rx_Drop);		//Rx_Drop bit set high
		ReadAddress(RxBuff_Addr, RxBuff_Data);	//The last (unique) received byte is taken from register Rx_Buff
		assert (RxBuff_Data == '0)
			$display("PASS imm 2: Rx Drop case - Rx_Buff is 0");
		else begin
			$display("FAIL imm 2: Rx Drop case - Rx_Buff is NOT 0");
			ErrCntImmAssertions++;
		end
		
		waitClock(50);		//50 clock cycles to ensure all data is processed.
	endtask
	
	task TB_Assertion3_13();
		logic [7:0] RxSC_Data;
		logic [5:0][7:0] HDLC_Data;
		logic [5:0][8:0] Data_FrameError;	//One extra bit to generate FrameError
		logic [129:0][7:0] Overflow_Data;
		logic [1:0][7:0] FCS_Data;
	
		//Overflow input data is received
		HDLC_genFlag(0);
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(Overflow_Data), Overflow_Data);	//Sends more data than allowed for "Information" field
		MakeRxStimulus($size(Overflow_Data), $size(Overflow_Data[0]), Overflow_Data);
		HDLC_genFCS($size(Overflow_Data), Overflow_Data, FCS_Data);
		MakeRxStimulus($size(FCS_Data), $size(FCS_Data[0]), FCS_Data);
		HDLC_genFlag(0);
		
		@(posedge uin_hdlc.Rx_Ready);			//Wait until the Rx data is ready
		ReadAddress(RxSC_Addr, RxSC_Data);		//All readable bits from register Rx_SC are checked
		assert (RxSC_Data[0] == 1'b1) $display ("PASS imm 3: Overflow case - Rx_Buff has valid data");
			else begin $display("FAIL imm 3: Overflow case - Rx_Buff does NOT have valid data"); ErrCntImmAssertions++; end
		assert (RxSC_Data[2] == 1'b0) $display ("PASS imm 3: Overflow case - No Frame error");
			else begin $display("FAIL imm 3: Overflow case - Frame error asserted"); ErrCntImmAssertions++; end
		assert (RxSC_Data[3] == 1'b0) $display ("PASS imm 3: Overflow case - No Abort signal");
			else begin $display("FAIL imm 3: Overflow case - Abort signal asserted"); ErrCntImmAssertions++; end
		assert (RxSC_Data[4] == 1'b1) $display ("PASS imm 3: Overflow case - Overflow signal asserted");
			else begin $display("FAIL imm 3: Overflow case - No Overflow signal"); ErrCntImmAssertions++; end
		
		waitClock(50);		//50 clock cycles to ensure all data is processed.
		
		//Aborted frame signal is received
		HDLC_genFlag(0);
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(HDLC_Data), HDLC_Data);
		MakeRxStimulus($size(HDLC_Data), $size(HDLC_Data[0]), HDLC_Data);
		HDLC_genFlag(1);	//Abort flag generate (before current HDLC frame is finished)
		
		@(negedge uin_hdlc.Rx_AbortDetect);		//Wait until the Abort signal is really detected
		ReadAddress(RxSC_Addr, RxSC_Data);		//All readable bits from register Rx_SC are checked
		assert (RxSC_Data[0] == 1'b0) $display ("PASS imm 3: Abort case - Rx_Buff does NOT have valid data");
			else begin $display("FAIL imm 3: Abort case - Rx_Buff has valid data"); ErrCntImmAssertions++; end
		assert (RxSC_Data[2] == 1'b0) $display ("PASS imm 3: Abort case - No Frame error");
			else begin $display("FAIL imm 3: Abort case - Frame error asserted"); ErrCntImmAssertions++; end
		assert (RxSC_Data[3] == 1'b1) $display ("PASS imm 3: Abort case - Abort Signal asserted");
			else begin $display("FAIL imm 3: Abort case - No Abort signal"); ErrCntImmAssertions++; end
		assert (RxSC_Data[4] == 1'b0) $display ("PASS imm 3: Abort case - No Overflow signal");
			else begin $display("FAIL imm 3: Abort case - Overflow signal asserted"); ErrCntImmAssertions++; end
		
		waitClock(50);		//50 clock cycles to ensure all data is processed.		
		
		//Frame error is detected
		HDLC_genFlag(0);
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(Data_FrameError), Data_FrameError);
		MakeRxStimulus($size(Data_FrameError), $size(Data_FrameError[0]), Data_FrameError);
		//The whole frame must have extra bits to activate FrameError (so nothing else sent, as module consider FCS the last 2 bytes before flag)
		HDLC_genFlag(0);
		
		@(posedge uin_hdlc.Rx_FrameError);		//Wait until the Frame Error is really detected
		ReadAddress(RxSC_Addr, RxSC_Data);		//All readable bits from register Rx_SC are checked
		assert (RxSC_Data[0] == 1'b0) $display ("PASS imm 3: FrameError case - Rx_Buff does NOT have valid data");
			else begin $display("FAIL imm 3: FrameError case - Rx_Buff has valid data"); ErrCntImmAssertions++; end
		assert (RxSC_Data[2] == 1'b1) $display ("PASS imm 3: FrameError case - Frame Error asserted");
			else begin $display("FAIL imm 3: FrameError case - No Frame Error"); ErrCntImmAssertions++; end
		assert (RxSC_Data[3] == 1'b0) $display ("PASS imm 3: FrameError case - No Abort signal");
			else begin $display("FAIL imm 3: FrameError case - Abort signal asserted"); ErrCntImmAssertions++; end
		assert (RxSC_Data[4] == 1'b0) $display ("PASS imm 3: FrameError case - No Overflow signal");
			else begin $display("FAIL imm 3: FrameError case - Overflow signal asserted"); ErrCntImmAssertions++; end

		waitClock(50);		//50 clock cycles to ensure all data is processed.		

		//Normal frame (with no errors) is received
		HDLC_genFlag(0);
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(HDLC_Data), HDLC_Data);
		MakeRxStimulus($size(HDLC_Data), $size(HDLC_Data[0]), HDLC_Data);
		HDLC_genFCS($size(HDLC_Data), HDLC_Data, FCS_Data);
		MakeRxStimulus($size(FCS_Data), $size(FCS_Data[0]), FCS_Data);
		HDLC_genFlag(0);

		@(posedge uin_hdlc.Rx_Ready);			//Wait until the Rx data is ready
		ReadAddress(RxSC_Addr, RxSC_Data);		//All readable bits from register Rx_SC are checked
		assert (RxSC_Data[0] == 1'b1) $display ("PASS imm 3: Normal case - Rx_Buff has data to read");
			else begin $display("FAIL imm 3: Normal case - Rx_Buff not prepared yet"); ErrCntImmAssertions++; end
		assert (RxSC_Data[2] == 1'b0) $display ("PASS imm 3: Normal case - No Frame error");
			else begin $display("FAIL imm 3: Normal case - Frame error asserted"); ErrCntImmAssertions++; end
		assert (RxSC_Data[3] == 1'b0) $display ("PASS imm 3: Normal case - No Abort signal");
			else begin $display("FAIL imm 3: Normal case - Abort signal asserted"); ErrCntImmAssertions++; end
		assert (RxSC_Data[4] == 1'b0) $display ("PASS imm 3: Normal case - No Overflow signal");
			else begin $display("FAIL imm 3: Normal case - Overflow signal asserted"); ErrCntImmAssertions++; end
		
		waitClock(50);		//50 clock cycles to ensure all data is processed.
	endtask
			
	task TB_Assertion4();
		logic [3:0][7:0] HDLC_Data;

		for(int i=0; i<$size(HDLC_Data); i++) begin     //Random data loaded into Tx_Buff (to be transmitted later)
			HDLC_Data[i] = $urandom();
			WriteAddress(TxBuff_Addr, HDLC_Data[i]);
		end
		WriteAddress(TxSC_Addr, Tx_Enable);     //Tx_Enable set high to start transmission

		for(int i=0; i<$size(HDLC_Data); i++) begin
			waitClock(1);
			assert (uin_hdlc.Tx_DataOutBuff == HDLC_Data[i])        //The whole Tx byte is compared with written one
				$display("PASS imm 4: Correct Tx output from Tx_Buff");
			else begin
				$display("FAIL imm 4: Not correct Tx output from Tx_Buff");
				ErrCntImmAssertions++;
			end
			if (i!=($size(HDLC_Data)-1)) @(posedge uin_hdlc.Tx_RdBuff);		//Wait until next byte is read from Tx buffer (except last iteration)
		end
		
		waitClock(20);          //20 clock cycles to ensure all data is processed.
	endtask
	
	task TB_Assertion5_12_14_15();
		logic [39:0][7:0] HDLC_Data;
		logic  [1:0][7:0] FCS_Data;

		HDLC_genFlag(0);		//One complete correct frame is sent
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(HDLC_Data), HDLC_Data);
		MakeRxStimulus($size(HDLC_Data), $size(HDLC_Data[0]), HDLC_Data);
		HDLC_genFCS($size(HDLC_Data), HDLC_Data, FCS_Data);
		MakeRxStimulus($size(FCS_Data), $size(FCS_Data[0]), FCS_Data);
		HDLC_genFlag(0);
		
		@(negedge uin_hdlc.Rx_EoF);             //Waits until Rx frame has been completely received
		assert (uin_hdlc.Rx_FrameSize == $size(HDLC_Data) + $size(FCS_Data))
			$display("PASS imm 14: FrameSize matches length of received frame");
		else begin
			$display("FAIL imm 14: FrameSize does NOT match length of received frame");
			ErrCntImmAssertions++;
		end
		
		waitClock(20);		//20 clock cycles to ensure all data is processed.
	endtask

	task TB_Assertion6();
		int NumBytes;	//Number of bytes to send
		NumBytes = 6;
		
		for(int i=0; i<NumBytes; i++)		//Specific value 127 is necessary for the concurrent assertion...
			WriteAddress(TxBuff_Addr, 8'b01111111);
		WriteAddress(TxSC_Addr, Tx_Enable);			//Tx enabled to send the data out 

		@(posedge uin_hdlc.Tx_ValidFrame);			//Wait until Tx frame is valid
		for(int i=0; i<(10*NumBytes); i++) begin
			waitClock(1);			//Rx updated with as many bits as set in Tx (8 bits/byte + up to 2 0s due to zero insertion)
			uin_hdlc.Rx = uin_hdlc.Tx;
		end
		HDLC_genFlag(0);	//End flag sequence to set Rx to Idle (Tx module sent start flag sequence before)
		
		waitClock(20);		//20 clock cycles to ensure all data is processed.
	endtask
	
	task TB_Assertion7();
		$display("PASS conc 7: Dummy assertion. It only waits 50 clock cycles to check if Tx!=1 during IDLE");
		waitClock(50);		//50 clock cycles to ensure system keeps in idle state.
	endtask
	
	task TB_Assertion8_10();
		logic [39:0][7:0] HDLC_Data;

		HDLC_genFlag(0);
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(HDLC_Data), HDLC_Data);
		MakeRxStimulus($size(HDLC_Data), $size(HDLC_Data[0]), HDLC_Data);
		HDLC_genFlag(1);	//Abort flag generate (before current HDLC frame is finished)
		
		waitClock(20);		//20 clock cycles to ensure all data is processed.
	endtask
	
	task TB_Assertion9();
		for(int i=0; i<4; i++)	//Random data loaded into Tx_Buff (to be transmitted later)
			WriteAddress(TxBuff_Addr, $urandom());
		
		WriteAddress(TxSC_Addr, Tx_Enable);	//Tx_Enable set high to start transmission
		waitClock(10);		//10 clock cycles to ensure all data is processed.
		WriteAddress(TxSC_Addr, Tx_Enable + Tx_AbortFrame);	//Abort signal requested (Tx_Enable should continue high)
		
		waitClock(100);		//100 clock cycles to ensure all data is processed.
	endtask

	task TB_Assertion11();
		logic [5:0][7:0] HDLC_Data;		//48 bits of input data
		logic [1:0][7:0] CRC_manual;	//16 bits of CRCs
		logic [1:0][7:0] CRC_automatic;
		int NumBytes;

		NumBytes = 6;	//The input data is composed by 6 bytes
		HDLC_Data = 48'b10010100_00000001_11111111_11111111_11111111_11111111;	//Input data defined
		CRC_manual = {HDLC_Data[NumBytes-1], HDLC_Data[NumBytes-2]};	//CRC generated manually
		HDLC_Data[NumBytes-1] = '0;
		HDLC_Data[NumBytes-2] = '0;
		
		HDLC_genFCS($size(HDLC_Data), HDLC_Data, CRC_automatic);	//CRC generated automatically
		
		assert (CRC_manual == CRC_automatic)	//Manual and automatic CRC should match
			$display("PASS imm 11: CRC correctly generated");
		else begin
			$display("FAIL imm 11: CRC NOT correctly generated");
			ErrCntImmAssertions++;
		end
		
		waitClock(20);		//20 clock cycles to ensure all data is processed.
	endtask
	
	task TB_Assertion16();
		logic [7:0][7:0] HDLC_Data;
		logic [5:0][8:0] Data_FrameError;	//One extra bit to generate "Non-byte aligned" error

		//Non-byte aligned case generated
		HDLC_genFlag(0);	
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(Data_FrameError), Data_FrameError);
		MakeRxStimulus($size(Data_FrameError), $size(Data_FrameError[0]), Data_FrameError);
		//The whole frame must have extra bits to activate FrameError (so nothing else sent, as module consider FCS the last 2 bytes before flag)
		HDLC_genFlag(0);
		
		waitClock(20);		//20 clock cycles to ensure all data is processed.
		
		//FCS error case generated
		WriteAddress(RxSC_Addr, Rx_FCSen);	//Checking of FCS in Rx enabled
		HDLC_genFlag(0);
		HDLC_genAddr();
		HDLC_genControl();
		HDLC_genInfo($size(HDLC_Data), HDLC_Data);
		MakeRxStimulus($size(HDLC_Data), $size(HDLC_Data[0]), HDLC_Data);
		HDLC_genFlag(0);	//The module will consider FCS as the last two bytes from Rx input (so result will be wrong)
		
		waitClock(20);		//20 clock cycles to ensure all data is processed.
	endtask
	
	task TB_Assertion17();
		for(int i=0; i<4; i++)		//Random data loaded into Tx_Buff (to be transmitted later)
			WriteAddress(TxBuff_Addr, $urandom());
		WriteAddress(TxSC_Addr, Tx_Enable);	//Tx_Enable set high to start transmission
		
		waitClock(100);		//100 clock cycles to ensure all data is processed.
	endtask
	
	task TB_Assertion18();
		logic [7:0] TxSC_Data;
		
		for(int i=0; i<130; i++)	//130 bytes (more than allowed) of random data loaded into Tx_Buff (to be transmitted later)
			WriteAddress(TxBuff_Addr, $urandom());
		WriteAddress(TxSC_Addr, Tx_Enable);	//Tx_Enable set high to start transmission
		
		ReadAddress(TxSC_Addr, TxSC_Data);
		assert (TxSC_Data[4] == 1'b1)	//Bit 4 of register TxSC is Tx_Full
			$display("PASS imm 18: Tx_Full asserted after passing size limit");
		else begin
			$display("FAIL imm 18: Tx_Full NOT asserted after passing size limit");
			ErrCntImmAssertions++;
		end
		
		waitClock(100);		//100 clock cycles to ensure all data is processed.
	endtask

endprogram