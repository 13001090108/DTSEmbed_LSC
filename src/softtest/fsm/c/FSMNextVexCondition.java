package softtest.fsm.c;

import org.w3c.dom.Node;

import softtest.cfg.c.*;
/**
 * 状态产生点条件判断当前控制流节点是否为状态的产生点。
 * 通常在控制流上状态只要经过一个节点后该条件就会返回true。
 * 在目前的DTSCpp版本中并没有实际使用该条件。
 * @author zys	
 * 2010-4-21
 */
public class FSMNextVexCondition extends FSMCondition {
	@Override
	public boolean evaluate(FSMMachineInstance fsm, FSMStateInstance state,
			VexNode vex) {
		boolean b = false;
		if (state.getVexNode() == vex) {
			b = false;
		} else {
			b = true;
		}
		return b;
	}

	/** 解析xml */
	@Override
	public void loadXML(Node n) {
		if (fsm != null && fsm.getRelatedClass() != null) {
			loadAction(n, fsm.getRelatedClass());
		}
	}
}
