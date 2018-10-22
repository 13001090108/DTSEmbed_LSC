package softtest.fsm.c;

import org.w3c.dom.Node;

import softtest.cfg.c.*; 
import softtest.ast.c.*;
import softtest.symboltable.c.*;

/** 
 * 变量作用域条件只能出现在变量相关的状态机中，判断当前控制流节点对应的作用域在变量声明作用域外面还是里面。
 * isout标记指示取在外面还是在里面情况作为evaluate的真值返回。 
 * */
public class FSMScopeCondition extends FSMCondition {
	private boolean isout = false;

	/** 对条件进行计算，判断其是否满足 */
	@Override
	public boolean evaluate(FSMMachineInstance fsm, FSMStateInstance state,
			VexNode vex) {
		boolean b = false;
		VariableNameDeclaration v = fsm.getRelatedVariable();
		if (v != null) {
			Scope delscope = v.getScope();
			SimpleNode astnode = vex.getTreenode();
			if (isout) {
				if (!astnode.getScope().isSelfOrAncestor(delscope)) {
					// 声明作用域已经不是当前作用域自己或父亲了
					b = true;
				} else if (delscope.isSelfOrAncestor(astnode.getScope())
						&& delscope != astnode.getScope() && vex.isBackNode()) {
					// 当前作用域是声明作用域自己或者父亲，但是当前节点需要终止当前作用域
					b = true;
				} else {
					b = false;
				}
			} else {
				if (astnode.getScope().isSelfOrAncestor(delscope)) {
					// 当前作用域在声明作用域里面
					b = true;
				} else {
					b = false;
				}
			}
		}
		if (b) {
			if (relatedmethod == null) {
				b = true;
			} else {
				Object[] args = new Object[2];
				args[0] = vex;
				args[1] = fsm;
				try {
					Boolean r = (Boolean) relatedmethod.invoke(null, args);
					b = r;
				} catch (Exception e) {
					 e.printStackTrace();
					throw new RuntimeException("action error",e);
				}
			}
		}
		return b;
	}

	/** 解析xml */
	@Override
	public void loadXML(Node n) {
		Node type = n.getAttributes().getNamedItem("Type");
		if (type.getNodeValue().equals("out")) {
			isout = true;
		}

		if (fsm != null && fsm.getRelatedClass() != null) {
			loadAction(n, fsm.getRelatedClass());
		}
	}
}
