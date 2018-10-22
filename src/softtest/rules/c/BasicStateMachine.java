package softtest.rules.c;

import softtest.interpro.c.InterContext;
import softtest.summary.c.MethodPostCondtionVisitor;

public class BasicStateMachine {

	public void registFetureVisitors() {
		InterContext.addPostConditionVisitor(MethodPostCondtionVisitor.getInstance());
	}
}
