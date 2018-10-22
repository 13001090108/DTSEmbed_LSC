package softtest.fsm.c;

import java.util.*;

import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.analysis.ValueSet;
import softtest.fsm.c.FSMStateInstance;

/** 状态实例集合 */
public class FSMStateInstanceSet {
	/** 状态实例hash表 */
	private Hashtable<FSMStateInstance, FSMStateInstance> table = new Hashtable<FSMStateInstance, FSMStateInstance>();

	/** 构造函数 */
	public FSMStateInstanceSet() {

	}

	/** 拷贝构造函数 */
	public FSMStateInstanceSet(FSMStateInstanceSet set) {
		for (Enumeration<FSMStateInstance> e = set.table.elements(); e
				.hasMoreElements();) {
			FSMStateInstance newinstance = new FSMStateInstance(e.nextElement());
			table.put(newinstance, newinstance);
		}
	}

	/** 加入状态实例 */
	public void addStateInstance(FSMStateInstance stateinstance) {
		if (stateinstance.getState().isFinal()) {
			// 如果是终结状态则不加入
			return;
		}
		FSMStateInstance si = table.get(stateinstance);
		if (si != null) {
			// 该状态实例已经存在了,应该考虑条件的合并
			si.setSymbolDomainSet(SymbolDomainSet.union(si.getSymbolDomainSet(), stateinstance.getSymbolDomainSet()));
			si.mergeValueSet(stateinstance.getValueSet(),stateinstance.getSymbolDomainSet());
			si.getVarDomainSet();
		} else {
			// 直接加入
			si = new FSMStateInstance(stateinstance);
			table.put(si, si);
		}

	}
	
	/**
	 * 加入状态，不考虑状态对应区间的合并
	 */
	public void addStateInstanceWithoutConditon(FSMStateInstance stateinstance) {
		if (stateinstance.getState().isFinal()) {
			// 如果是终结状态则不加入
			return;
		}
		FSMStateInstance si = table.get(stateinstance);
		if (si == null) {
			si= new FSMStateInstance(stateinstance);
			table.put(si, si);
		}
	}

	/** 移除状态实例 */
	public void removeStateInstance(FSMStateInstance stateinstance) {
		table.remove(stateinstance);
	}

	/** 获得状态实例哈希表 */
	public Hashtable<FSMStateInstance, FSMStateInstance> getTable() {
		return table;
	}

	/** 根据当前控制流节点，计算状态集合的所有状态条件 */
	public void calDomainSet(VexNode vex) {
		List<FSMStateInstance> todelete = new ArrayList<FSMStateInstance>();
		for (Enumeration<FSMStateInstance> e = table.elements(); e
				.hasMoreElements();) {
			FSMStateInstance s = e.nextElement();
			s.calDomainSet(vex);
			if (s.getVarDomainSet().isContradict()) {
				todelete.add(s);
			}
		}
		// 删除那些矛盾状态
		Iterator<FSMStateInstance> i = todelete.iterator();
		while (i.hasNext()) {
			table.remove(i.next());
		}
	}
	
	/** 根据前趋控制流判断节点和是否为真分支标志，计算状态集合的所有状态条件 */
	public void calCondition(VexNode pre,boolean istruebranch) {
		List<FSMStateInstance> todelete = new ArrayList<FSMStateInstance>();
		for (Enumeration<FSMStateInstance> e = table.elements(); e
				.hasMoreElements();) {
			FSMStateInstance s = e.nextElement();
			s.calCondition(pre,istruebranch);
			if (s.getVarDomainSet().isContradict()) {
				todelete.add(s);
			}
		}
		// 删除那些矛盾状态
		Iterator<FSMStateInstance> i = todelete.iterator();
		while (i.hasNext()) {
			table.remove(i.next());
		}
	}
	
	/** 根据caselabel节点和switch节点，计算状态集合的所有状态条件 */
	public void calSwitch(VexNode n, VexNode pre) {
		List<FSMStateInstance> todelete = new ArrayList<FSMStateInstance>();
		for (Enumeration<FSMStateInstance> e = table.elements(); e
				.hasMoreElements();) {
			FSMStateInstance s = e.nextElement();
			s.calSwitch(n, pre);
			if (s.getVarDomainSet().isContradict()) {
				todelete.add(s);
			}
		}
		// 删除那些矛盾状态
		Iterator<FSMStateInstance> i = todelete.iterator();
		while (i.hasNext()) {
			table.remove(i.next());
		}
	}
	
	/** 打印 */
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		sb.append("{");
		boolean b = false;
		for (Enumeration<FSMStateInstance> e = table.elements(); e
				.hasMoreElements();) {
			FSMStateInstance s = e.nextElement();
			sb.append(s + ",");
			b = true;
		}
		if (b) {
			sb.setCharAt(sb.length() - 1, '}');
		} else {
			sb.append("}");
		}
		return sb.toString();
	}

	/** 判断状态集合是否为空集 */
	public boolean isEmpty() {
		return table.isEmpty();
	}
}
