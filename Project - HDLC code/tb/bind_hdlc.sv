module bind_hdlc ();
	bind test_hdlc assertions_hdlc u_assertion_bind(		//This binding already refers to the module files "test_hdlc" and "assertions_hdlc"
		.ErrCntConcAssertions	(uin_hdlc.ErrCntConcAssertions),	//(concurrent assertions file), which are all in the same folder, so it is not 
		.Clk				(uin_hdlc.Clk),					//necessary to write any "include" statement...
		.Rst				(uin_hdlc.Rst),
		//Tx elements (1 real output + variables)
		.Tx					(uin_hdlc.Tx),					//Connections direction is: ".input properties file(input module file)"
		.Tx_ValidFrame		(uin_hdlc.Tx_ValidFrame),		//AGAIN, THIS IS FOR CONCURRENT ASSERTIONS ONLY!!!
		.Tx_AbortedTrans	(uin_hdlc.Tx_AbortedTrans),
		.Tx_WriteFCS		(uin_hdlc.Tx_WriteFCS),
		.Tx_InitZero		(uin_hdlc.Tx_InitZero),
		.Tx_StartFCS		(uin_hdlc.Tx_StartFCS),
		.Tx_RdBuff			(uin_hdlc.Tx_RdBuff),
		.Tx_NewByte			(uin_hdlc.Tx_NewByte),
		.Tx_FCSDone			(uin_hdlc.Tx_FCSDone),
		.Tx_Data			(uin_hdlc.Tx_Data),
		.Tx_Done			(uin_hdlc.Tx_Done),
		.Tx_Full			(uin_hdlc.Tx_Full),
		.Tx_DataAvail		(uin_hdlc.Tx_DataAvail),
		.Tx_FrameSize		(uin_hdlc.Tx_FrameSize),
		.Tx_DataArray		(uin_hdlc.Tx_DataArray),
		.Tx_DataOutBuff		(uin_hdlc.Tx_DataOutBuff),
		.Tx_WrBuff			(uin_hdlc.Tx_WrBuff),
		.Tx_Enable			(uin_hdlc.Tx_Enable),
		.Tx_DataInBuff		(uin_hdlc.Tx_DataInBuff),
		.Tx_AbortFrame		(uin_hdlc.Tx_AbortFrame),
		//Rx elements (1 real input + variables)
		.Rx					(uin_hdlc.Rx),
		.Rx_ValidFrame		(uin_hdlc.Rx_ValidFrame),
		.Rx_WrBuff			(uin_hdlc.Rx_WrBuff),
		.Rx_EoF				(uin_hdlc.Rx_EoF),
		.Rx_AbortSignal		(uin_hdlc.Rx_AbortSignal),
		.Rx_StartZeroDetect	(uin_hdlc.Rx_StartZeroDetect),
		.Rx_FrameError		(uin_hdlc.Rx_FrameError),
		.Rx_StartFCS		(uin_hdlc.Rx_StartFCS),
		.Rx_StopFCS			(uin_hdlc.Rx_StopFCS),
		.Rx_Data			(uin_hdlc.Rx_Data),
		.Rx_NewByte			(uin_hdlc.Rx_NewByte),
		.Rx_FlagDetect		(uin_hdlc.Rx_FlagDetect),
		.Rx_AbortDetect		(uin_hdlc.Rx_AbortDetect),
		.RxD				(uin_hdlc.RxD),
		.Rx_FCSerr			(uin_hdlc.Rx_FCSerr),
		.Rx_Ready			(uin_hdlc.Rx_Ready),
		.Rx_FrameSize		(uin_hdlc.Rx_FrameSize),
		.Rx_Overflow		(uin_hdlc.Rx_Overflow),
		.Rx_DataBuffOut		(uin_hdlc.Rx_DataBuffOut),
		.Rx_FCSen			(uin_hdlc.Rx_FCSen),
		.Rx_RdBuff			(uin_hdlc.Rx_RdBuff),
		.Rx_Drop			(uin_hdlc.Rx_Drop)
	);
endmodule