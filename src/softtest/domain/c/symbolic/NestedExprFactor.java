package softtest.domain.c.symbolic;

import java.util.Iterator;

import softtest.cfg.c.VexNode;
import softtest.domain.c.analysis.SymbolDomainSet;
import softtest.domain.c.interval.Domain;

public class NestedExprFactor extends Factor implements Cloneable{
	@Override
	public String toString() {
		return "("+expression.toString()+")";
	}

	@Override
	public Object clone() throws CloneNotSupportedException {
		NestedExprFactor factor=(NestedExprFactor)super.clone();
		if(factor.expression!=null){
			factor.expression=(Expression)expression.clone();
		}
		return factor;
	}

	private Expression expression;
	
	public Expression getExpression() {
		return expression;
	}

	public void setExpression(Expression expression) {
		this.expression = expression;
	}

	public NestedExprFactor(Expression expression) {
		super();
		this.expression = expression;
	}

	@Override
	public int hashCode() {
		final int PRIME = 31;
		int result = 1;
		result = PRIME * result + ((expression == null) ? 0 : expression.hashCode());
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
		final NestedExprFactor other = (NestedExprFactor) obj;
		if (expression == null) {
			if (other.expression != null)
				return false;
		} else if (!expression.equals(other.expression))
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
			return 1;
		}
		if(o instanceof NestedExprFactor){
			NestedExprFactor exprfactor=(NestedExprFactor)o;
			return expression.compareTo(exprfactor.expression);
		}
		return -1;	
	}
	
	@Override
	public Factor flatten(int depth) {
		super.flatten(depth);
		Factor ret=this;
        Expression expr =expression.flatten(depth);
        if (expr.getTerms().size() == 1) {
			Iterator<Term> it = expr.getTerms().iterator();
			Term t = it.next();
			if (t.getPowers().size() == 1 && t.getOperator().equals("+")) {
				Iterator<Power> ip = t.getPowers().iterator();
				Power p = ip.next();
				if (p.getFactors().size() == 1 && p.getOperator().equals("*")) {
					Iterator<Factor> ifa = p.getFactors().iterator();
					Factor f = ifa.next();
					return f;
				}
			}
		}       
		return ret;
	}

	@Override
	public Domain getDomain(SymbolDomainSet ds) {
		return expression.getDomain(ds);
	}
}
