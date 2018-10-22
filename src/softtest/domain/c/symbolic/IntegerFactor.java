package softtest.domain.c.symbolic;

import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.interval.IntegerDomain;
import softtest.symboltable.c.Type.*;

public class IntegerFactor extends NumberFactor {
	private long value=0;
	
	public IntegerFactor(long value) {
		this.value = value;
		this.type=CType_BaseType.getBaseType("int");
	}
	
	public long getValue() {
		return value;
	}
	
	public void setValue(long value) {
		this.value = value;
	}

	@Override
	public boolean equals(Object obj) {
		if (this == obj)
			return true;
		if (obj == null)
			return false;
		if (getClass() != obj.getClass())
			return false;
		IntegerFactor other = (IntegerFactor) obj;
		if (value != other.value)
			return false;
		return true;
	}

	@Override
	public int hashCode() {
		final int prime = 31;
		int result = 1;
		result = prime * result + (int) (value ^ (value >>> 32));
		return result;
	}

	@Override
	public String toString() {
		return ""+value;
	}

	@Override
	public int compareTo(Factor o) {
		if(o instanceof NumberFactor){
			return 0;
		}
		return -1;
	}
	
	@Override
	public NumberFactor numAdd(NumberFactor o){
		if(o instanceof DoubleFactor){
			DoubleFactor other=(DoubleFactor)o;
			return new DoubleFactor(other.getValue()+(double)value);
		}
		if(o instanceof IntegerFactor){
			IntegerFactor other=(IntegerFactor)o;
			return new IntegerFactor(other.getValue()+value);
		}
		throw new RuntimeException("the operand can only be num factor");
	}
	
	@Override
	public NumberFactor numSub(NumberFactor o){
		if(o instanceof DoubleFactor){
			DoubleFactor other=(DoubleFactor)o;
			return new DoubleFactor((double)value-other.getValue());
		}
		if(o instanceof IntegerFactor){
			IntegerFactor other=(IntegerFactor)o;
			return new IntegerFactor(value-other.getValue());
		}
		throw new RuntimeException("the operand can only be num factor");
	}
	
	@Override
	public NumberFactor numMul(NumberFactor o){
		if(o instanceof DoubleFactor){
			DoubleFactor other=(DoubleFactor)o;
			return new DoubleFactor(other.getValue()*(double)value);
		}
		if(o instanceof IntegerFactor){
			IntegerFactor other=(IntegerFactor)o;
			return new IntegerFactor(other.getValue()*value);
		}
		throw new RuntimeException("the operand can only be num factor");
	}
	
	@Override
	public NumberFactor numDiv(NumberFactor o){
		if(o instanceof DoubleFactor){
			DoubleFactor other=(DoubleFactor)o;
			return new DoubleFactor((double)value/other.getValue());
		}
		if(o instanceof IntegerFactor){
			IntegerFactor other=(IntegerFactor)o;
			//return new IntegerFactor(value/other.getValue());
			return new DoubleFactor((double)value/other.getValue());
		}
		throw new RuntimeException("the operand can only be num factor");
	}

	@Override
	public double getDoubleValue() {
		return (double)value;
	}

	@Override
	public NumberFactor numMinus() {
		return new IntegerFactor(-value);
	}


	@Override
	public Domain getDomain(SymbolDomainSet ds) {
		return new IntegerDomain(value,value);
	}
}
