package softtest.domain.c.symbolic;

import softtest.config.c.Config;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.interval.Domain;
import softtest.symboltable.c.Type.*;

public class SymbolFactor extends Factor {
	private String symbol;
	
	public SymbolFactor(String symbol) {
		super();
		if(Config.TEST_SYMBOLIC){
			this.symbol = symbol;
		}else{
			this.symbol = symbol+name_count++;
		}
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + ((symbol == null) ? 0 : symbol.hashCode());
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
		SymbolFactor other = (SymbolFactor) obj;
		if (symbol == null) {
			return false;
		} else if (symbol.equals(other.symbol)){
			return true;
		}
		return false;
	}

	public String getSymbol() {
		return symbol;
	}

	public void setSymbol(String symbol) {
		this.symbol = symbol;
	}
	
	@Override
	public String toString() {
		return symbol;
	}
	
	@Override
	public int compareTo(Factor o) {
		if(o instanceof NumberFactor){
			return 1;
		}
		if(o instanceof SymbolFactor){
			SymbolFactor f=(SymbolFactor)o;
			return symbol.compareTo(f.symbol);
		}
		
		return -1;
	}

	@Override
	public Factor flatten(int depth) {
		super.flatten(depth);
		return this;
	}
	
	private static long name_count=0;
	
	public static SymbolFactor genSymbol(CType type){
		String name="S_"+name_count++;
		SymbolFactor ret=new SymbolFactor(name);
		if(type==null){
			type=CType_BaseType.getBaseType("int");
		}
		ret.setType(type);
		return ret;
	}
	
	public static SymbolFactor genSymbol(CType type,String str){
		String name=str+"_"+name_count++;
		SymbolFactor ret=new SymbolFactor(name);
		if(type==null){
			type=CType_BaseType.getBaseType("int");
		}
		ret.setType(type);
		return ret;
	}
	
	@Override
	public Domain getDomain(SymbolDomainSet ds) {
		if(ds!=null){
			return ds.getDomain(this);
		}else{
			return null;
		}
	}
	
	public Domain getDomainWithoutNull(SymbolDomainSet ds){
		Domain domain=getDomain(ds);
		if(domain==null){
			return Domain.getFullDomainFromType(type);
		}
		//如果条件判断为参数的话，则全区间为unknown，为了减少漏报，应将unknown设置为该类型的全集
		//modified by zhouhb
		if(domain.isUnknown()){
			return Domain.getFullDomainFromType(type);
		}else{
			return domain;
		}
//		return domain;
	}
	
	public static void resetNameCount(){
		name_count=0;
	}
}
