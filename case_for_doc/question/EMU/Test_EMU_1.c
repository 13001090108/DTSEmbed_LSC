typedef enum Q1{Q1Send, Q1Recv} Q1;
	typedef enum Q2{Q2None, Q2Send, Q2Recv} Q2;
	// Inconsistency between switch variable and case labels
	void foo1(Q1 q){
	  switch (q){
	    case Q2Send: f(); break;
	    case Q2Recv: g(); break;
	  }
	}
	//Inconsistency between case labels
	void foo2(Q1 q){
	  switch (q){
	    case Q1Send: f(); break;
	    case Q2Recv: g(); break;
	  }
	}
