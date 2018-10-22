package softtest.fsm.c;

import org.w3c.dom.Node;

import softtest.cfg.c.*;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.PointerDomain;
import softtest.domain.c.interval.PointerValue;
import softtest.symboltable.c.*;
import softtest.symboltable.c.Type.*;
/** 
变量域条件只能出现在路径敏感且变量相关的状态机中，
判断当前变量的取值范围和条件的domain相等或不等。
isequal标记指示取相等还是不等。
 */
public class FSMDomainCondition extends FSMCondition {
	public FSMDomainCondition() {
		
	}
	/** 域类型 */
	private CType type = CType_BaseType.intType;

	/** 域值 */
	private Domain domain = null;

	/** 相等还是不等标记 */
	private boolean isequal = true;

	/** 对条件进行计算，判断其是否满足 */
	@Override
	public boolean evaluate(FSMMachineInstance fsmin, FSMStateInstance state,
			VexNode vex) {
		boolean b = false;
		if (!fsmin.getFSMMachine().isPathSensitive()
				|| !fsmin.getFSMMachine().isVariableRelated()) {
			throw new RuntimeException(
					"Domain condition can not apply to this kind of fsm.");
		}
		VariableNameDeclaration v = fsmin.getRelatedVariable();
		if (v == null) {
			return false;
		}
		Domain d1=null, d2=null;
		d1 = Domain.castToType(domain, type);
		if (vex.getDomain(v)==null) {
			return false;
		}
		d2 = Domain.castToType(vex.getDomain(v), type);
		if (d1.equals(d2)) {
			b = true;
		}

		if (!isequal) {
			b = !b;
		}
		if (b)
		{
			if (relatedmethod == null)
			{
				b = true;
			} else
			{
				Object[] args = new Object[2];
				args[0] = vex;
				args[1] = fsm;
				try
				{
					Boolean r = (Boolean) relatedmethod.invoke(null, args);
					b = r;
				} catch (Exception e)
				{
					// e.printStackTrace();
					throw new RuntimeException("action error",e);
				}
			}
		}
		return b;
	}

	/** 将字符串转换为内部的值，当前只支持引用类型 */
	// Add by liaobh
	public void parseString(String strtype, String strvalue) {

		if ("POINT".equals(strtype)) {
			type = new CType_Pointer();
			domain = new PointerDomain(PointerValue.valueOf(strvalue));
		}
		if (type instanceof CType_Pointer) {
			domain = PointerDomain.castToType(domain, type);
		}
	}

	// End by liaobh

	/** 打印 */
	@Override
	public String toString() {
		StringBuffer b = new StringBuffer();
		if (!isequal) {
			b.append("not ");
		}
		b.append(domain);
		return b.toString();
	}

	/** 解析xml */
	@Override
	public void loadXML(Node n) {
		Node type = n.getAttributes().getNamedItem("Type");
		Node value = n.getAttributes().getNamedItem("Value");
		if (type == null || value == null) {
			throw new RuntimeException(
					"Domain condition must have a type and a value.");
		}
		Node equal = n.getAttributes().getNamedItem("Equal");
		if (equal != null) {
			if (equal.getNodeValue().equals("false")) {
				isequal = false;
			}
		}
		parseString(type.getNodeValue(), value.getNodeValue());
		if (fsm != null && fsm.getRelatedClass() != null) {
			loadAction(n, fsm.getRelatedClass());
		}
	}
}
