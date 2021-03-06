package softtest.domain.c.analysis;

import java.util.ArrayList;
import java.util.Collections;
import java.util.List;

import softtest.cfg.c.Edge;
import softtest.cfg.c.VexNode;
import softtest.domain.c.interval.Domain;
import softtest.domain.c.symbolic.Expression;
import softtest.domain.c.symbolic.SymbolFactor;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.Type.CType_BaseType;

public class NarrowingCalculation extends IterationCalculation {
	@Override
	public void iterationExec(VexNode iterationHead) {
		counter++;
		String nodeName=iterationHead.getName();
		
		List<Edge> list = new ArrayList<Edge>();
		for (Edge e:iterationHead.getInedges().values()) {
			VexNode v=e.getTailNode();
			String name=v.getName();
			if(name.startsWith("continue"))
				continue;
			list.add(e);
		}
		Collections.sort(list);
		
		if(nodeName.startsWith("while_head") || nodeName.startsWith("for_head"))
		{
			VexNode preIterationNode=null;
			VexNode postIterationNode=null;
			if(list.size()==2){
				preIterationNode=list.get(0).getTailNode();
				postIterationNode=list.get(1).getTailNode();
			}else if(list.size()==1){//存在跳转，没有到循环头结点的回边，见回归测试用例112
				calculateOver=true;
				domainChanged=false;
				return;
			}
			if(postIterationNode.getContradict() || preIterationNode.getContradict()){
				calculateOver=true;
				domainChanged=false;
				return;
			}
			List<VariableNameDeclaration> varList=getLeftVar(iterationHead);//获取循环中的所有条件变量
			VariableNameDeclaration v=varList.get(0);//暂时只处理单条件变量的情况，如while(i<100)
			Expression valueExpr=null;
			
			if(isIterationOver()){
				Expression postExpr=postIterationNode.getValueSet().getValue(v);
				Domain postDomain=postExpr.getDomain(SymbolDomainSet.intersect(
						iterationHead.getCondata().getTrueMayDomainSet(),iterationHead.getSymDomainset()));
				Expression preExpr=preIterationNode.getValueSet().getValue(v);
				Domain preDomain=null;
				if(preExpr!=null)
					preDomain=preExpr.getDomain(iterationHead.getSymDomainset());
				
				Domain domain=Domain.union(postDomain, preDomain, v.getType());
				//在widening之前先调整域的类型为一致
				if(domain!=null && lastDomain!=null && domain.getDomaintype()!=lastDomain.getDomaintype())
					domain=Domain.castToType(domain, CType_BaseType.getBaseType(lastDomain.getDomaintype().name()));
				domain=Domain.narrowingDomain(lastDomain, domain);
				lastVarDomainSet=VarDomainSet.narrowing(lastVarDomainSet, iterationHead.getVarDomainSet(),iterationHead);
				
				SymbolFactor s=SymbolFactor.genSymbol(v.getType(), v.getImage());
				valueExpr=new Expression(s);
				iterationHead.getValueSet().addValue(v, valueExpr);
				iterationHead.addSymbolDomain(s, domain);
				
				if(lastDomain!=null)
				{
					domainChanged=isDomainChanged(lastDomain,domain);
				}
				lastDomain=domain;
			}
		}else if(nodeName.startsWith("do_while_out1")){
			//do-while循环的头结点只有一条入边
			VexNode postIterationNode=null;
			if(list.size()==1){
				postIterationNode=list.get(0).getTailNode();
			}else{
				calculateOver=true;
				domainChanged=false;
				return;
			}
			if(postIterationNode.getContradict()){
				calculateOver=true;
				domainChanged=false;
				return;
			}
			List<VariableNameDeclaration> varList=getLeftVar(iterationHead);//获取循环中的所有条件变量
			VariableNameDeclaration v=varList.get(0);//暂时只处理单条件变量的情况，如while(i<100)
			Expression valueExpr=null;
			if(isIterationOver()){
				Expression postExpr=postIterationNode.getValueSet().getValue(v);
				Domain domain=postExpr.getDomain(iterationHead.getSymDomainset());
				domain=Domain.castToType(domain, v.getType());
					
				domain=Domain.narrowingDomain(lastDomain, domain);
				lastVarDomainSet=VarDomainSet.narrowing(lastVarDomainSet, iterationHead.getVarDomainSet(),iterationHead);

				SymbolFactor s=SymbolFactor.genSymbol(v.getType(), v.getImage());
				valueExpr=new Expression(s);
				iterationHead.getValueSet().addValue(v, valueExpr);
				iterationHead.addSymbolDomain(s, domain);
					
				if(lastDomain!=null)
				{
					domainChanged=isDomainChanged(lastDomain,domain);
				}
				lastDomain=domain;
			}
		}
	}
}
