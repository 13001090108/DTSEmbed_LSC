package softtest.DefUseAnalysis.c;

import java.io.Serializable;
import java.util.*;



import softtest.ast.c.*;
import softtest.symboltable.c.*;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;

public class LiveDefsSet implements Serializable{
	/** 变量到达定义出现哈希表 */
	Hashtable<VariableNameDeclaration, Hashtable<SimpleNode, NameOccurrence>> table = new Hashtable<VariableNameDeclaration, Hashtable<SimpleNode, NameOccurrence>>();

	/** 获得变量到达定义出现哈希表 */
	public Hashtable<VariableNameDeclaration, Hashtable<SimpleNode, NameOccurrence>> getTable() {
		return table;
	}

	/** 设置变量到达定义出现哈希表 */
	public void setTable(Hashtable<VariableNameDeclaration, Hashtable<SimpleNode, NameOccurrence>> table) {
		this.table = table;
	}

	public void clear()
	{
		table.clear();
	}
	
	/** 设置变量的新定义 */
	public void setNewDef(NameOccurrence occ) {
		if (occ.getOccurrenceType() != NameOccurrence.OccurrenceType.DEF && occ.getOccurrenceType() != OccurrenceType.DEF_AFTER_USE) {
			return;
		}
		if (occ.getDeclaration() == null || !(occ.getDeclaration() instanceof VariableNameDeclaration)) {
			return;
		}
		VariableNameDeclaration v = (VariableNameDeclaration) occ.getDeclaration();
		Hashtable<SimpleNode, NameOccurrence> occs = table.get(v);
		if (occs == null) {
			occs = new Hashtable<SimpleNode, NameOccurrence>();
			table.put(v, occs);
		}

		for (Enumeration<NameOccurrence> e = occs.elements(); e.hasMoreElements();) {
			NameOccurrence o = e.nextElement();
			o.addDefUndef(occ);
			occ.addUndefDef(o);
		}
		occs.clear();
		occs.put(occ.getLocation(), occ);
	}

	/** 增加变量到达定义出现 */
	public void addLiveDef(NameOccurrence occ) {
		if (occ.getOccurrenceType() != NameOccurrence.OccurrenceType.DEF && occ.getOccurrenceType() != OccurrenceType.DEF_AFTER_USE) {
			return;
		}
		if (occ.getDeclaration() == null || !(occ.getDeclaration() instanceof VariableNameDeclaration)) {
			return;
		}
		VariableNameDeclaration v = (VariableNameDeclaration) occ.getDeclaration();
		Hashtable<SimpleNode, NameOccurrence> occs = table.get(v);
		if (occs == null) {
			occs = new Hashtable<SimpleNode, NameOccurrence>();
			table.put(v, occs);
		}
		occs.put(occ.getLocation(), occ);
	}

	/** 合并到达定义表 */
	public void mergeLiveDefs(LiveDefsSet set) {
		Set<Map.Entry<VariableNameDeclaration, Hashtable<SimpleNode, NameOccurrence>>> entryset = set.getTable().entrySet();
		Iterator<Map.Entry<VariableNameDeclaration, Hashtable<SimpleNode, NameOccurrence>>> i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<VariableNameDeclaration, Hashtable<SimpleNode, NameOccurrence>> entry = i.next();
			// VariableNameDeclaration v=entry.getKey();
			Hashtable<SimpleNode, NameOccurrence> occs = entry.getValue();
			for (Enumeration<NameOccurrence> e = occs.elements(); e.hasMoreElements();) {
				NameOccurrence o = e.nextElement();
				addLiveDef(o);
			}
		}
	}

	/** 获得变量的到达定义 */
	public ArrayList<NameOccurrence> getVariableLiveDefs(VariableNameDeclaration v) {
		ArrayList<NameOccurrence> list = new ArrayList<NameOccurrence>();
		Hashtable<SimpleNode, NameOccurrence> occs = table.get(v);
		if (occs != null) {
			for (Enumeration<NameOccurrence> e = occs.elements(); e.hasMoreElements();) {
				NameOccurrence o = e.nextElement();
				list.add(o);
			}
		}
		return list;
	}	
	//added by cmershen,2016.11.4
	public ArrayList<NameOccurrence> getOccs() {
		ArrayList<NameOccurrence> list = new ArrayList<NameOccurrence>();
		for(Hashtable<SimpleNode, NameOccurrence> ht : getTable().values()){
			for(NameOccurrence occ:ht.values())
				list.add(occ);
		}
		return list;
	}
	/** 打印 */
	@Override
	public String toString() {
		StringBuffer b = new StringBuffer();
		Set<Map.Entry<VariableNameDeclaration, Hashtable<SimpleNode, NameOccurrence>>> entryset = getTable().entrySet();
		Iterator<Map.Entry<VariableNameDeclaration, Hashtable<SimpleNode, NameOccurrence>>> i = entryset.iterator();
		while (i.hasNext()) {
			Map.Entry<VariableNameDeclaration, Hashtable<SimpleNode, NameOccurrence>> entry = i.next();
			VariableNameDeclaration v=entry.getKey();
			//b.append("   "+v.getImage()+":");
			Hashtable<SimpleNode, NameOccurrence> occs = entry.getValue();
			//zys:对变量出现进行排序,排序原则是按照变量出现的行号，具体见Comparator的实现方式	2010.3.4
			ArrayList list=new ArrayList(occs.values());
			//支持对数组下标的访问
			//add by zhouhb
			//2011.3.23
			if(v.getType()!=null&&v.getType().isArrayType()&&!list.isEmpty()){
				NameOccurrence no=(NameOccurrence)list.get(0);
				
				b.append("   "+no.getImage()+":");
			}else{
				b.append("   "+v.getImage()+":");
			}
			Comparator comparator=new Comparator(){
				public int compare(Object arg0, Object arg1) {
					if(arg0 instanceof NameOccurrence && arg1 instanceof NameOccurrence)
					{
						NameOccurrence occ1=(NameOccurrence)arg0;
						NameOccurrence occ2=(NameOccurrence)arg1;
						return (occ1.getLocation().getBeginLine()
									-occ2.getLocation().getBeginLine())>0?1:-1;
					}
					return 0;
				}
			};
			Collections.sort(list,comparator);
			for(Iterator it=list.iterator();it.hasNext();)
			{
				NameOccurrence o=(NameOccurrence)it.next();
				b.append("("+o.getOccurrenceType()+") ["+o.getLocation().getBeginLine()+"Line,"+o.getLocation().getBeginColumn()+"Column]");
			}
//			for (Enumeration<NameOccurrence> e = occs.elements(); e.hasMoreElements();) {
//				NameOccurrence o = e.nextElement();
//				b.append(" ["+o.getLocation().getBeginLine()+","+o.getLocation().getBeginColumn()+"]");
//			}
		}
		return b.toString();
	}
}
