interface in_hdlc ();			//An interface encapsulates the inputs, outputs (and intermediate signals is needed) of a module,
	//Tb						//so they can be used without referring directly to the module itself, improving readability.
	int ErrCntConcAssertions;

	//Clock and reset
	logic Clk;
	logic Rst;

	// Address
	logic [2:0] Address;
	logic       WriteEnable;
	logic       ReadEnable;
	logic [7:0] DataIn;
	logic [7:0] DataOut;

	// TX
	logic Tx;
	logic TxEN;

	// RX
	logic Rx;
	logic RxEN;

	// Tx - internal
	logic       Tx_ValidFrame;		//Transmitting valid TX frame
	logic       Tx_AbortedTrans;	//TX transmission is aborted
	logic       Tx_WriteFCS;		//Transmit FCS byte
	logic       Tx_InitZero;		//Initialize zero insertion with two first bytes of TX buffer
	logic       Tx_StartFCS;		//Start FCS calculation
	logic       Tx_RdBuff;			//Read new byte from TX buffer
	logic       Tx_NewByte;			//New byte is loaded to be transmitted
	logic       Tx_FCSDone;			//Finished calculating FCS bytes
	logic [7:0] Tx_Data;			//Next TX byte to be transmitted
	logic       Tx_Done;			//TX buffer can be written
	logic       Tx_Full;			//TX buffer is full
	logic       Tx_DataAvail;		//Data is available in TX buffer
	logic [7:0] Tx_FrameSize; 		//Number of bytes in TX buffer
	logic [127:0][7:0] Tx_DataArray;//TX buffer
	logic [7:0] Tx_DataOutBuff;		//Next TX byte in buffer to be transmitted
	logic       Tx_WrBuff;			//Write new byte to TX buffer
	logic       Tx_Enable;			//Start transmission of TX buffer
	logic [7:0] Tx_DataInBuff;		//Data from write operation
	logic       Tx_AbortFrame;		//Abort current TX frame

	// Rx - internal
	logic       Rx_ValidFrame;		//Receiving valid frame
	logic       Rx_WrBuff;			//Write RX byte to buffer
	logic       Rx_EoF;				//Whole RX frame has been received (end of frame)
	logic       Rx_AbortSignal;		//RX frame was aborted
	logic       Rx_StartZeroDetect;	//Start detecting inserted zeros
	logic       Rx_FrameError;		//Error in received RX frame
	logic       Rx_StartFCS;		//Start FCS calculation
	logic       Rx_StopFCS;			//Stop FCS calculation
	logic [7:0] Rx_Data;			//Received RX byte
	logic       Rx_NewByte;			//New RX byte has been received
	logic       Rx_FlagDetect;		//Flag detected
	logic       Rx_AbortDetect;		//Abort detected
	logic       RxD;				//Delayed RX bit (9 clock cycles)
	logic       Rx_FCSerr;			//Frame Check Sequence error
	logic       Rx_Ready;			//RX Buffer ready to be read
	logic [7:0] Rx_FrameSize;		//Number of bytes received (minus FCS bytes)
	logic       Rx_Overflow;		//RX buffer is full
	logic [7:0] Rx_DataBuffOut;		//Data read from RX buffer
	logic       Rx_FCSen;			//FCS error detection enabled
	logic       Rx_RdBuff;			//Read byte from RX buffer
	logic       Rx_Drop;			//Drop received RX frame

	// Others
	logic       ZeroDetect;

endinterface