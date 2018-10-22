package softtest.fsm.c;

import java.util.*;

import softtest.cfg.c.*;
import softtest.config.c.Config;

/** 状态机实例集合 */
public class FSMMachineInstanceSet {
	/** 存储状态机实例的hash表 */
	private Hashtable<FSMMachineInstance, FSMMachineInstance> table = new Hashtable<FSMMachineInstance, FSMMachineInstance>();

	/** 构造函数 */
	public FSMMachineInstanceSet() {

	}

	/** 拷贝构造函数 */
	public FSMMachineInstanceSet(FSMMachineInstanceSet set) {
		for (Enumeration<FSMMachineInstance> e = set.table.elements(); e
				.hasMoreElements();) {
			FSMMachineInstance newinstance = new FSMMachineInstance(e
					.nextElement());
			table.put(newinstance, newinstance);
		}
	}

	/** 清空状态机实例 */
	public void clear() {
		if(Config.FSM_STATISTIC){
			for(FSMMachineInstance instance : table.keySet()){
				String fsmname=instance.getFSMMachine().getName();
				Integer count=FSMMachine.statistic.get(fsmname);
				if(count!=null){
					count--;
					try{
					if(count<0){
						throw new RuntimeException(fsmname+" = "+count+" error!");
					}else if(count==0){
						FSMMachine.statistic.remove(fsmname);
					}else{
						FSMMachine.statistic.put(fsmname, count);
					}
					}catch(RuntimeException e){
						e.printStackTrace();
						continue;
					}
				}
			}
		}
		table.clear();
	}

	/** 获得状态机实例hash表 */
	public Hashtable<FSMMachineInstance, FSMMachineInstance> getTable() {
		return table;
	}

	/** 设置状态机实例hash表 */
	public void setTable(Hashtable<FSMMachineInstance, FSMMachineInstance> table) {
		this.table = table;
	}

	/** 将状态机集合set合并进来 */
	public void mergeFSMMachineInstances(FSMMachineInstanceSet set) {
		Hashtable<FSMMachineInstance, FSMMachineInstance> addtable = set.table;
		for (Enumeration<FSMMachineInstance> e = addtable.elements(); e
				.hasMoreElements();) {
			FSMMachineInstance addfsmin = e.nextElement();
			FSMMachineInstance fsmin = table.get(addfsmin);
			if (fsmin != null) {
				// 该状态机在集合中已经存在，合并状态
				for (Enumeration<FSMStateInstance> f = addfsmin.getStates()
						.getTable().elements(); f.hasMoreElements();) {
					fsmin.addStateInstance(f.nextElement());
				}
			} else {
				// 该状态机在集合中不存在，加入
				fsmin = new FSMMachineInstance(addfsmin);
				table.put(fsmin, fsmin);
			}
		}
	}
	
	/** 不考虑状态转化，将状态机集合，set合并进来 */
	public void mergFSMMachineInstancesWithoutConditon(FSMMachineInstanceSet set) {
		Hashtable<FSMMachineInstance, FSMMachineInstance> addtable = set.table;
		for (FSMMachineInstance addfsmin : addtable.keySet()) {
			FSMMachineInstance fsmin = table.get(addfsmin);
			if (fsmin != null) {
				for (FSMStateInstance state : addfsmin.getStates().getTable().keySet()) {
					fsmin.addStateInstanceWithoutConditon(state);
				}
			} else {
				// 该状态机在集合中不存在，加入
				fsmin = new FSMMachineInstance(addfsmin);
				table.put(fsmin, fsmin);
			}
		}
	}

	/** 将状态机实例集合list加入进来 */
	public void addFSMMachineInstances(List list) {
		Iterator i = list.iterator();
		while (i.hasNext()) {
			FSMMachineInstance in = (FSMMachineInstance) i.next();
			if (!table.containsKey(in)) {
				table.put(in, in);
			}
		}
	}

//	/** 增加状态条件约束 */
//	public void addDomainSet(DomainSet set) {
//		for (Enumeration<FSMMachineInstance> e = table.elements(); e
//				.hasMoreElements();) {
//			FSMMachineInstance f = e.nextElement();
//			f.addDomainSet(set);
//		}
//	}

	/** 打印 */
	@Override
	public String toString() {
		StringBuffer sb = new StringBuffer();
		boolean b = false;
		for (Enumeration<FSMMachineInstance> e = table.elements(); e
				.hasMoreElements();) {
			FSMMachineInstance f = e.nextElement();
			sb.append(f + "\n");
			b = true;
		}
		if (b) {
			return sb.substring(0, sb.length() - 2);
		} else {
			return sb.toString();
		}
	}

	/** 根据当前控制流节点，计算状态机集合的所有状态条件 */
	public void calSwitch(VexNode n, VexNode pre) {
		List<FSMMachineInstance> todelete = new ArrayList<FSMMachineInstance>();
		for (Enumeration<FSMMachineInstance> e = table.elements(); e
				.hasMoreElements();) {
			FSMMachineInstance f = e.nextElement();
			f.calSwitch(n, pre);
			if (f.getStates().isEmpty()) {
				todelete.add(f);
			}
		}
		// 删除那些空的状态机
		Iterator<FSMMachineInstance> i = todelete.iterator();
		while (i.hasNext()) {
			table.remove(i.next());
		}
	}

	/** 根据前趋控制流判断节点和是否为真分支标志，计算状态机集合的所有状态条件 */
	public void calCondition(VexNode pre, boolean istruebranch) {
		List<FSMMachineInstance> todelete = new ArrayList<FSMMachineInstance>();
		for (Enumeration<FSMMachineInstance> e = table.elements(); e
				.hasMoreElements();) {
			FSMMachineInstance f = e.nextElement();
			f.calCondition(pre, istruebranch);
			if (f.getStates().isEmpty()) {
				todelete.add(f);
			}
		}
		// 删除那些空的状态机
		Iterator<FSMMachineInstance> i = todelete.iterator();
		while (i.hasNext()) {
			table.remove(i.next());
		}
	}

	/** 根据当前控制流节点，计算状态机集合中的所有状态条件 */
	public void calDomainSet(VexNode vex) {
		List<FSMMachineInstance> todelete = new ArrayList<FSMMachineInstance>();
		for (Enumeration<FSMMachineInstance> e = table.elements(); e
				.hasMoreElements();) {
			FSMMachineInstance f = e.nextElement();
			f.calDomainSet(vex);
			if (f.getStates().isEmpty()) {
				todelete.add(f);
			}
		}
		// 删除那些空的状态机
		Iterator<FSMMachineInstance> i = todelete.iterator();
		while (i.hasNext()) {
			table.remove(i.next());
		}
	}
}
