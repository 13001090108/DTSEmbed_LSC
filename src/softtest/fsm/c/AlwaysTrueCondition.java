package softtest.fsm.c;

import org.w3c.dom.Node;
import softtest.cfg.c.*;

/** 
如果没有关联动作方法则该条件永远返回true，
如果存在关联动作方法则返回关联动作方法的返回值。
 */
public class AlwaysTrueCondition extends FSMCondition {

	/** 对条件进行计算，判断其是否满足 */
	@Override
	public boolean evaluate(FSMMachineInstance fsm, FSMStateInstance state,
			VexNode vex) {
		boolean b = true;
		if (relatedmethod == null) {
			b = true;
		} else {
			Object[] args = new Object[2];
			args[0] = vex;
			args[1] = fsm;
			try {
				Object obj = relatedmethod.invoke(null, args);
				if(obj instanceof Boolean)
				{
					b = (Boolean)obj;
				}
			} catch (Exception e) {
				e.printStackTrace();
				throw new RuntimeException("action error",e);
			}
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
