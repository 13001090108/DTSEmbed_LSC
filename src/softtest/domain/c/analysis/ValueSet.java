package softtest.domain.c.analysis;

import java.util.*;

import softtest.cfg.c.VexNode;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.symbolic.*;
import softtest.symboltable.c.*;

public class ValueSet {
	private Hashtable<VariableNameDeclaration, Expression> valuetable = new Hashtable<VariableNameDeclaration, Expression>();
	
	/** 缺省构造函数 */
	public ValueSet() {

	}

	/** 拷贝构造函数 ,当前并没有进行深层拷贝*/
	public ValueSet(ValueSet as) {
		Expression value = null;
		Hashtable<VariableNameDeclaration, Expression> table=as.valuetable;
		for(VariableNameDeclaration v : table.keySet()){
			value =table.get(v);
			addValue(v, value);
		}
	}

	/** 设置变量v的抽象取值 */
	public Expression addValue(VariableNameDeclaration v, Expression value) {
		return valuetable.put(v, value);
	}

	/** 获得变量v的抽象取值 */
	public Expression getValue(VariableNameDeclaration v) {
		//add by cmershen,2016.9.2
		if(valuetable!=null)
			return valuetable.get(v);
		else
			return null;	
	}
	
	/** 清除哈希表 */
	public void clearValueSet() {
		valuetable.clear();
	}

	/** 设置哈希表 */
	public void setTable(Hashtable<VariableNameDeclaration, Expression> valuetable) {
		this.valuetable = valuetable;
	}

	/** 获得哈希表 */
	public Hashtable<VariableNameDeclaration, Expression> getTable() {
		return valuetable;
	}
	
	/** 判断哈希表是否为空 */
	public boolean isEmpty() {
		return valuetable.isEmpty();
	}
	
	/** 打印 */
	@Override
	public String toString() {
		StringBuffer b = new StringBuffer();
		if (valuetable.size() == 0) {
			b.append("empty");
			return b.toString();
		}
		
		Expression d = null;
		for(VariableNameDeclaration v : valuetable.keySet()){
			d =valuetable.get(v);
			b.append(v.getImage() + ":" + d+ "  ");
		}
		return b.toString();
	}
	
	public HashSet<SymbolFactor> getAllSymbol(){
		HashSet<SymbolFactor> ret=new HashSet<SymbolFactor>();
		
		Expression d = null;
		for(VariableNameDeclaration v : valuetable.keySet()){
			d =valuetable.get(v);
			ret.addAll(d.getAllSymbol());
		}
		return ret;
	}
	/*
	 * 移除那些超出当前控制流节点作用域的变量
	 */
	public void removeOutScopeVar(VexNode vex) {
		ValueSet temp = new ValueSet();
		Set<Map.Entry<VariableNameDeclaration, Expression>> entryset = vex.getValueSet().getTable().entrySet();
		Iterator<Map.Entry<VariableNameDeclaration, Expression>> i = entryset.iterator();
		Expression d1 = null;
		VariableNameDeclaration v1 = null;
		while (i.hasNext()) {
			Map.Entry<VariableNameDeclaration, Expression> e = i.next();
			v1 = e.getKey();
			d1 = e.getValue();
			if (vex.getTreenode().getScope().isSelfOrAncestor(v1.getScope())) {
				temp.getTable().put(v1, d1);
			}
		}
		this.valuetable = temp.getTable();
	}
}
