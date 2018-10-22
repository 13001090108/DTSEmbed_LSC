package softtest.domain.c.symbolic;

import java.util.*;

import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.interval.Domain;

public class FunctionFactor extends Factor implements Cloneable {
    private String name;
    
    private List<Expression> paramlist;
    
    private boolean mathfunction;

	public FunctionFactor(String name, List<Expression> paramList) {
		super();
		this.name = name;
		this.paramlist = paramList;
	}

	public String getName() {
		return name;
	}

	public void setName(String name) {
		this.name = name;
	}

	public List<Expression> getParamlist() {
		return paramlist;
	}

	public void setParamlist(List<Expression> paramlist) {
		this.paramlist = paramlist;
	}

	public boolean isMathfunction() {
		return mathfunction;
	}

	public void setMathfunction(boolean mathfunction) {
		this.mathfunction = mathfunction;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (mathfunction ? 1231 : 1237);
		result = prime * result + ((name == null) ? 0 : name.hashCode());
		result = prime * result
				+ ((paramlist == null) ? 0 : paramlist.hashCode());
		return result;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		FunctionFactor other = (FunctionFactor) obj;
		if (mathfunction != other.mathfunction)
			return false;
		if (name == null) {
			if (other.name != null)
				return false;
		} else if (!name.equals(other.name))
			return false;
		if (paramlist == null) {
			if (other.paramlist != null)
				return false;
		} else if (!paramlist.equals(other.paramlist))
			return false;
		return true;
	}
	
	@Override
	public int compareTo(Factor o) {
		if(o instanceof NumberFactor){
			return 1;
		}
		if(o instanceof SymbolFactor){
			return 1;
		}
		
		if(o instanceof FunctionFactor){
			FunctionFactor f=(FunctionFactor)o;
			return name.compareTo(f.name);
		}
		
		return -1;
	}

	@Override
	public Factor flatten(int depth) {
		super.flatten(depth);
		Factor ret=null;
		ArrayList<Expression> list=new ArrayList<Expression>();
		for(Expression e:paramlist){
			list.add(e.flatten(depth));
		}
		ret=new FunctionFactor(name,list);
		return ret;
	}
	
	public Object clone() throws CloneNotSupportedException {
		FunctionFactor f=(FunctionFactor)super.clone();
		f.paramlist=new ArrayList<Expression>();
		for(Expression e:paramlist){
			f.paramlist.add((Expression)e.clone());
		}
		return f;
	}

	@Override
	public Domain getDomain(SymbolDomainSet ds) {
		// TODO 没有实现
		return null;
	}
}
