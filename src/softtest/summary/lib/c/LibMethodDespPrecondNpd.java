package softtest.summary.lib.c;

import java.util.List;

import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.SimpleNode;
import softtest.interpro.c.ScopeType;
import softtest.interpro.c.Variable;
import softtest.rules.c.StateMachineUtils;
import softtest.summary.c.MethodFeatureType;
import softtest.summary.c.MethodSummary;
import softtest.summary.gcc.fault.MethodNPDPreCondition;
import softtest.symboltable.c.VariableNameDeclaration;

/**
 * <p>The NPD Precondition MFD which load from the XML, which adds MethodNPDPreCondition feature into summary</p>
 * @author Qi Peng
 *
 */
public class LibMethodDespPrecondNpd extends LibMethodDesp {

	public LibMethodDespPrecondNpd(MethodFeatureType type, Object value) {
		super(type, value);
	}

	public void createFeature(String libName, SimpleNode node, MethodSummary mtSummary) {
		MethodNPDPreCondition npdPre = new MethodNPDPreCondition();
		String xpath = ".//FunctionDeclaration//ParameterTypeList/ParameterList/ParameterDeclaration[" + value + "]/Declarator";
		List<SimpleNode> nodes = StateMachineUtils.getEvaluationResults(node, xpath);
		if (nodes == null || nodes.size() == 0) {
			return;
		}
		ASTDeclarator qid = (ASTDeclarator)nodes.get(0);
		VariableNameDeclaration varDecl = (VariableNameDeclaration)qid.getVariableNameDeclaration();
		Variable variable = new Variable(ScopeType.METHOD_SCOPE, varDecl.getImage(), varDecl.getType());
		variable.setParamIndex(varDecl.getParamIndex());
		variable.setScopeName(libName);
		//decl.setVariable(var);
		if (variable != null) {
			npdPre.addVariable(variable, ""/*methodName + " on lib file " + libName*/);
		}
		mtSummary.addPreCondition(npdPre);
	}

}
