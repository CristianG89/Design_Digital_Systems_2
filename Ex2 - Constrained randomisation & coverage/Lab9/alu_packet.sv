//Make your struct here
typedef struct {
	rand bit [31:0] a;
	rand bit [31:0] b;
	rand bit [2:0] op;
} data_t;
	
class alu_data;
	//Initialize your struct here	
	rand data_t data;
	
	// Class methods(tasks) go here
	task get_data(ref bit [31:0] a1, ref bit [31:0] b1, ref bit [2:0] op1);
		a1 = data.a;
		b1 = data.b;
		op1 = data.op;
	endtask

	// Constraints
	constraint c1 { data.a inside {[0:127]}; }
	constraint c2 { data.b inside {[0:255]}; }
	constraint c3 { data.op inside {[0:6]}; }

endclass: alu_data
