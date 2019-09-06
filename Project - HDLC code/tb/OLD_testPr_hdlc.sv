// testPr_hdlc contains the Testbench (so simulation) as well as immediate assertions

//"program" defines a testbench (SV introduces this statement for testbench, instead of "module", with small differences...)
program testPr_hdlc (in_hdlc uin_hdlc);	//"uin_hdlc" is an instantiation of the interface "in_hdlc"
	int TbErrorCnt;
	parameter TxSC_Addr		= 3'b000;	//Address of register TxSC
	parameter TxBuff_Addr	= 3'b001;	//Address of register TxBuff
	parameter RxSC_Addr		= 3'b010;	//Address of register RxSC
	parameter RxBuff_Addr	= 3'b011;	//Address of register RxBuff
	parameter RxLen_Addr	= 3'b100;	//Address of register RxLen
	
	//"initial-begin" and "final-begin" statements are the simulation code
	initial begin	//Code inside "initial-end" is done once at the beginning of testbench
		$display("*************************************************************");
		$display("%t - Starting Test Program", $time);
		$display("*************************************************************");

		TB_Init();		//Testbench initialization

		//Receive(Size, NonByteAligned, Overflow, Abort, FCSerr, Drop, SkipRead)
		Receive( 26, 0, 0, 0, 0, 0, 0);	//Normal (no error set)
		Receive(126, 0, 1, 0, 0, 0, 0); //Overflow (overflow error set)
		Receive( 40, 0, 0, 1, 0, 0, 0); //Abort (abort error set)
		Receive( 30, 0, 0, 0, 1, 0, 0); //Frame error (frame error set)
		Receive( 20, 0, 0, 0, 0, 1, 0); //Drop (drop error set)
		Receive(126, 0, 0, 0, 0, 0, 0); //Normal
		//NOTE: Maximum Size is 126 bytes (128 - 2 FCS bytes)

		$display("*************************************************************");
		$display("%t - Finishing Test Program", $time);
		$display("*************************************************************");
		$stop;
	end

	final begin		//Code inside "final-end" is done once at the end of testbench
		$display("*********************************");
		$display("*                               *");
		$display("* \tAssertion Errors: %0d\t  *", TbErrorCnt + uin_hdlc.ErrCntAssertions);
		$display("*                               *");
		$display("*********************************");
	end

	task TB_Init();	//All inputs from "hdlc" module are fixed to stand-by value (defined inside "initial begin" statement)
		uin_hdlc.Clk         =   1'b0;
		uin_hdlc.Rst         =   1'b0;
		uin_hdlc.Address     = 3'b000;
		uin_hdlc.WriteEnable =   1'b0;
		uin_hdlc.ReadEnable  =   1'b0;
		uin_hdlc.DataIn      =     '0;
		uin_hdlc.TxEN        =   1'b1;
		uin_hdlc.Rx          =   1'b1;
		uin_hdlc.RxEN        =   1'b1;

		TbErrorCnt = 0;
		#1000ns;
		uin_hdlc.Rst         =   1'b1;
	endtask

	task WriteAddress(input logic [2:0] Address, input logic [7:0] Data);
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Address     = Address;
		uin_hdlc.WriteEnable = 1'b1;
		uin_hdlc.DataIn      = Data;
		@(posedge uin_hdlc.Clk);
		uin_hdlc.WriteEnable = 1'b0;
	endtask

	task ReadAddress(input logic [2:0] Address, output logic [7:0] Data);
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Address    = Address;
		uin_hdlc.ReadEnable = 1'b1;
		#100ns;
		Data                = uin_hdlc.DataOut;
		@(posedge uin_hdlc.Clk);
		uin_hdlc.ReadEnable = 1'b0;
	endtask

	task InsertRxFlagOrAbort(int flag);		//Function to insert either start/end or abort sequences
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b0;					//It starts with the least significant bit
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b1;
		@(posedge uin_hdlc.Clk);			//start/end sequence = 0111_1110
		uin_hdlc.Rx = 1'b1;					//abort sequence 	 = 1111_1110
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b1;
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b1;
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b1;
		@(posedge uin_hdlc.Clk);
		uin_hdlc.Rx = 1'b1;
		@(posedge uin_hdlc.Clk);
		if(flag)							//Start/end and abort sequences are just different
			uin_hdlc.Rx = 1'b1;				//in the most significant bit
		else
			uin_hdlc.Rx = 1'b0;
	endtask
	
	task MakeRxStimulus(logic [127:0][7:0] Data, int Size);
		logic [4:0] PrevData;
		PrevData = '0;
		for (int i=0; i<Size; i++) begin
			for (int j=0; j<8; j++) begin
				if(&PrevData) begin
					@(posedge uin_hdlc.Clk);
					uin_hdlc.Rx = 1'b0;
					PrevData = PrevData >> 1;
					PrevData[4] = 1'b0;
				end
				@(posedge uin_hdlc.Clk);
				uin_hdlc.Rx = Data[i][j];
				PrevData = PrevData >> 1;
				PrevData[4] = Data[i][j];
			end
		end
	endtask

	task GenerateFCSBytes(logic [127:0][7:0] data, int size, output logic[15:0] FCSBytes);
		logic [23:0] CheckReg;
		CheckReg[15:8]  = data[1];
		CheckReg[7:0]   = data[0];
		for(int i = 2; i < size+2; i++) begin
			CheckReg[23:16] = data[i];
			for(int j=0; j<8; j++) begin
				if(CheckReg[0]) begin
					CheckReg[0]    = CheckReg[0] ^ 1;
					CheckReg[1]    = CheckReg[1] ^ 1;
					CheckReg[13:2] = CheckReg[13:2];
					CheckReg[14]   = CheckReg[14] ^ 1;
					CheckReg[15]   = CheckReg[15];
					CheckReg[16]   = CheckReg[16] ^1;
				end
				CheckReg = CheckReg >> 1;
			end
		end
		FCSBytes = CheckReg;
	endtask

	// VerifyAbortReceive should verify correct value in Rx status/control register, and that Rx data buffer is zero after abort.
	task VerifyAbortReceive(logic [127:0][7:0] data, int Size);
		logic [7:0] ReadData;
		integer i;
		$display("VerifyAbortReceive starts!", $time);	//Always write functions after all variable declaration...

		ReadAddress(RxSC_Addr, ReadData);		//Rx_SC is read. It has address 0x2
		assert (ReadData[3] == 1'b1) $display ("PASS imm: Abort Signal asserted");	//Abort signal is bit nº3
			else $display("FAIL imm: No Abort signal");

		//Loop to read every byte (out of 127 bytes) of the received data
		i = 0;
		do begin 			//Verilog does not support "do while", but System Verilog does (structure only allowed in test-benches!)
			ReadAddress(RxBuff_Addr, ReadData);	//Rx_Buff is read. It has address 0x3
			assert (ReadData == 8'b0) //$display ("PASS imm: Rx_Buff in position %i is empty", i);		//Rx_SC must be empty.
				else $display("FAIL imm: Rx_Buff is not empty in position %i", i);
			i = i+1;	//POR LO VISTO ESTE BUCLE WHILE TIENE UN ENFOQUE SOFTWARE, AUNQUE NO ENTIENDO PORQUE...
		end
		while (i < Size);	//Loop as long as the incoming data
		$display("VerifyAbortReceive finished!", $time);
	endtask

	// VerifyDropReceive should verify correct value in Rx status/control register, and that Rx data buffer is zero after drop.
	task VerifyDropReceive(logic [127:0][7:0] data, int Size);
		logic [7:0] ReadData;
		integer i;
		$display("VerifyDropReceive starts!", $time);	//Always write functions after all variable declaration...

		ReadAddress(RxSC_Addr, ReadData);		//Rx_SC is read. It has address 0x2
		assert (ReadData[1] == 1'b1) $display ("PASS imm: Drop Signal asserted");		//Drop signal is bit nº1
			else $display("FAIL imm: No Drop signal");		//(ESTE BIT IS Write Only, POR TANTO ESTO NO APLICARÍA!!!)

		i = 0;
		do begin
			ReadAddress(RxBuff_Addr, ReadData);	//Rx_Buff is read. It has address 0x3
			assert (ReadData == 8'b0) //$display ("PASS imm: Rx_Buff in position %i is empty", i);		//Rx_SC must be empty.
				else $display("FAIL imm: Rx_Buff is not empty in position %i", i);
			i = i+1;
		end
		while (i < Size);
		$display("VerifyDropReceive finished!", $time);
	endtask
	
	// VerifyFrameErrReceive should verify correct value in Rx status/control register, and that Rx data buffer is zero after FCS error.
	task VerifyFrameErrReceive(logic [127:0][7:0] data, int Size);
		logic [7:0] ReadData;
		integer i;
		$display("VerifyFrameErrReceive starts!", $time);		//Always write functions after all variable declaration...

		ReadAddress(RxSC_Addr, ReadData);		//Rx_SC is read. It has address 0x2
		assert (ReadData[2] == 1'b1) $display ("PASS imm: Frame Error asserted");		//Frame error signal is bit nº5
			else $display("FAIL imm: No Frame Error");

		i = 0;
		do begin
			ReadAddress(RxBuff_Addr, ReadData);	//Rx_Buff is read. It has address 0x3
			assert (ReadData == 8'b0) //$display ("PASS imm: Rx_Buff in position %i is empty", i);		//Rx_SC must be empty.
				else $display("FAIL imm: Rx_Buff is not empty in position %i", i);
			i = i+1;
		end
		while (i < Size);
		$display("VerifyFrameErrReceive finished!", $time);
	endtask
	
	task VerifyOverflowReceive(logic [127:0][7:0] data, int Size);
		logic [7:0] ReadData;
		wait(uin_hdlc.Rx_Ready);
		$display("VerifyOverflowReceive starts!", $time);		//Always write functions after all variable declaration...

		ReadAddress(RxSC_Addr, ReadData);	//Rx_SC is read. It has address 0x2
		assert (ReadData[4] == 1'b1) $display ("PASS imm: Overflow signal asserted");	//Overflow signal is bit nº4	
			else $display("FAIL imm: No Overflow signal");
		$display("VerifyOverflowReceive finished!", $time);
	endtask
	
	// VerifyNormalReceive should verify correct value in Rx status/control register, and that Rx data buffer contains correct data.
	task VerifyNormalReceive(logic [127:0][7:0] data, int Size);
		logic [7:0] ReadData;
		integer i;
		wait(uin_hdlc.Rx_Ready);	//Rx_Ready indicates RX buffer is ready to be read
		$display("VerifyNormalReceive starts!", $time);	//Always write functions after all variable declaration...

		ReadAddress(RxSC_Addr, ReadData);		//Rx_SC is read. It has address 0x2
		assert (ReadData[0] == 1'b1) $display ("PASS imm: Rx_Buff has data to read");	//Rx_Ready signal is bit nº0 (TENIEDO UN WAIT ARRIBA, DBBO HACER ESTO??)
			else $display("FAIL imm: Rx_Buff not prepared yet");

		i = 0;
		do begin
			ReadAddress(RxBuff_Addr, ReadData);	//Rx_Buff is read. It has address 0x3
			assert (ReadData==data[i]) //$display ("PASS imm: Rx_Buff has correct data in position %i", i);		//The received data (argument) should match the read address
				else $display("FAIL imm: Rx_Buff has wrong data in position %i", i);
			i = i+1;
			end
		while (i < Size);
		$display("VerifyNormalReceive finished!", $time);
	endtask
	
	// Main Receive task
	task Receive(int Size, int NonByteAligned, int Overflow, int Abort, int FCSerr, int Drop, int SkipRead);
		logic [127:0][7:0] ReceiveData;		//128 bytes as maximum
		logic       [15:0] FCSBytes;
		logic   [2:0][7:0] OverflowData;
		logic       [7:0] caca;
		string msg;
		
		if (Size>8'd126)	//To be sure a bigger frame is not created
			Size = 8'd126;

		if(NonByteAligned)		//	NonByteAligned = $rose(Rx_FlagDetect) and $rose(!Rx_NewByte)
			msg = "- Non-byte aligned";
		else if(Overflow)
			msg = "- Overflow";
		else if(Abort)
			msg = "- Abort";
		else if(FCSerr)
			msg = "- FCS error";
		else if(Drop)
			msg = "- Drop";
		else if(SkipRead)
			msg = "- Skip read";
		else
			msg = "- Normal";
		$display("*************************************************************");
		$display("%t - Starting task Receive %s", $time, msg);
		$display("*************************************************************");

		//Random values introduced into "information" field of HDLC frame, to add them into the simulated Rx message
		for (int i=0; i<Size; i++) begin
			ReceiveData[i] = $urandom;	//$urandom = unsigned 32-bit integers random number
		end
		ReceiveData[Size]   = '0;		//The next 16 bits (for FCS) are set to 0 for security
		ReceiveData[Size+1] = '0;		//('0 puts number 0 with the requested bits quantity)

		//Calculate FCS bits, to add them into the simulated Rx message
		GenerateFCSBytes(ReceiveData, Size, FCSBytes);
		ReceiveData[Size]   = FCSBytes[7:0];
		ReceiveData[Size+1] = FCSBytes[15:8];

		//Enable FCS
		if(!Overflow && !NonByteAligned)
			WriteAddress(RxSC_Addr, 8'h20);	//Only "Rx_FCSen" is set to 1
		else
			WriteAddress(RxSC_Addr, 8'h00);	//No FCS in case of frame problem

		//Generate stimulus
		InsertRxFlagOrAbort(0);		//Start flag sequence is simulated as input to Rx module

		MakeRxStimulus(ReceiveData, Size + 2);	//Sends Address + Control + Information + FCS fields of HDLC frame

		if(Overflow) begin				//In case of overflow, sends extra data (FCS will become the last two bytes)
			OverflowData[0] = 8'h44;
			OverflowData[1] = 8'hBB;
			OverflowData[2] = 8'hCC;
			MakeRxStimulus(OverflowData, 3);
		end

		if(Abort)						//Depending on abort signal,
			InsertRxFlagOrAbort(1);		//either abort flag sequence is created
		else
			InsertRxFlagOrAbort(0);		//or end flag sequence is created
		
		//Incoming message discarded if requested
		if(Drop)
			WriteAddress(RxSC_Addr, 8'h02);

		@(posedge uin_hdlc.Clk);	//8 clock cycles (bits) where Rx input line is kept 1 (IDLE)
		uin_hdlc.Rx = 1'b1;
		repeat(8)	//Repeat the instruction below x (8 here) times
			@(posedge uin_hdlc.Clk);

		if(Overflow)
			VerifyOverflowReceive(ReceiveData, Size);
		else if(Abort)
			VerifyAbortReceive(ReceiveData, Size);
		else if(FCSerr)
			VerifyFrameErrReceive(ReceiveData, Size);
		else if(Drop) begin
			ReadAddress(RxSC_Addr, caca);		//TENIENDO DOS BITS Write Only, ES POSIBLE QUE LO IMPRIMA TODO???
			$display("Drop set. Current Rx_SC: 0x%h", caca);	//Print value in hex format
			VerifyDropReceive(ReceiveData, Size);
		end else if(!SkipRead)
			VerifyNormalReceive(ReceiveData, Size);

		#5000ns;		//5 milliseconds delay between each read HDLC frame
	endtask
	
endprogram