package softtest.summary.c;

import java.util.HashSet;
import java.util.Set;

import softtest.summary.c.MethodFeature;

public class MethodSummary {
	
	@Override
	public String toString() {
		StringBuffer sb=new StringBuffer();
		if(postConditions.size()>0){
			sb.append(postConditions);
			sb.append("\n");
		}
		if(preConditions.size()>0){
			sb.append(preConditions);
			sb.append("\n");
		}
		if(sideEffects.size()>0){
			sb.append(sideEffects);
		}
		return sb.toString();
	}

	/**
	 * 当前函数中记录函数副作用的函数特征集合
	 */
	private Set<MethodFeature> sideEffects;
	
	/**
	 * 当前函数中被调用之前需要满足前置条件的集合，比如函数非空的判断等
	 */
	private Set<MethodFeature> preConditions;
	
	/**
	 * 当前函数中被调用之后会产生的结果，比如函数返回值，对函数定义上下文中的变量值的更新
	 */
	private Set<MethodFeature> postConditions;
	
	public MethodSummary() {
		sideEffects = new HashSet<MethodFeature>();
		preConditions = new HashSet<MethodFeature>();
		postConditions = new HashSet<MethodFeature>();
	}
	
	public void addSideEffect(MethodFeature se) {
		sideEffects.add(se);
	}
	
	/*public void addSideEffectsAll(Set<MethodFeture> ses) {
		sideEffects.addAll(ses);
	}*/
	
	public void addPreCondition(MethodFeature preCond) {
		preConditions.add(preCond);
	}
	
	/*public void addPreConditionsAll(Set<MethodFeture> preConds) {
		preConditions.addAll(preConds);
	}*/
	
	public void addPostCondition(MethodFeature postCond) {
		postConditions.add(postCond);
	}
	
	/*public void addPostConditionsAll(Set<MethodFeture> postConds) {
		postConditions.addAll(postConds);
	}*/
	
	public Set<MethodFeature> getSideEffects() {
		return sideEffects;
	}
	
	public Set<MethodFeature> getPreConditions() {
		return preConditions;
	}
	
	public Set<MethodFeature> getPostConditions() {
		return postConditions;
	}
	
	public void addSummary(MethodSummary summary) {
		if (summary == null) {
			return;
		}
		Set<MethodFeature> temp = summary.getPostConditions();
		for (MethodFeature post: temp) {
			addPostCondition(post);
		}
		
		temp = summary.getPreConditions();
		for (MethodFeature post: temp) {
			addPreCondition(post);
		}
		
		temp = summary.getSideEffects();
		for (MethodFeature post: temp) {
			addSideEffect(post);
		}
	}
	public MethodFeature findMethodFeature(Class methodClass) {
		for (MethodFeature feature : sideEffects) {
			if (feature.getClass() == methodClass) {
				return feature;
			}
		}
		for (MethodFeature feature : preConditions) {
			if (feature.getClass() == methodClass) {
				return feature;
			}
		}
		for (MethodFeature feature : postConditions) {
			
//			if(feature.getName().equals("METHOD_POST_CONDITION"))//如果是feature是后置信息 added by lrt
//			{
//				return feature;
//			}
			//String str = feature.getClass().toString();
			if (feature.getClass() == methodClass) {
				return feature;
			}
		}
		return null;
	}
}
