package softtest.scvp.c;

import java.io.FileWriter;

import softtest.ast.c.ASTANDExpression;
import softtest.ast.c.ASTAbstractDeclarator;
import softtest.ast.c.ASTAdditiveExpression;
import softtest.ast.c.ASTArgumentExpressionList;
import softtest.ast.c.ASTAssignmentExpression;
import softtest.ast.c.ASTAssignmentOperator;
import softtest.ast.c.ASTCastExpression;
import softtest.ast.c.ASTCompoundStatement;
import softtest.ast.c.ASTConditionalExpression;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTConstantExpression;
import softtest.ast.c.ASTDeclaration;
import softtest.ast.c.ASTDeclarationList;
import softtest.ast.c.ASTDeclarationSpecifiers;
import softtest.ast.c.ASTDeclarator;
import softtest.ast.c.ASTDirectAbstractDeclarator;
import softtest.ast.c.ASTDirectDeclarator;
import softtest.ast.c.ASTEnumSpecifier;
import softtest.ast.c.ASTEnumerator;
import softtest.ast.c.ASTEnumeratorList;
import softtest.ast.c.ASTEqualityExpression;
import softtest.ast.c.ASTExclusiveORExpression;
import softtest.ast.c.ASTExpression;
import softtest.ast.c.ASTExpressionStatement;
import softtest.ast.c.ASTExternalDeclaration;
import softtest.ast.c.ASTFieldId;
import softtest.ast.c.ASTFunctionDeclaration;
import softtest.ast.c.ASTFunctionDefinition;
import softtest.ast.c.ASTIdentifierList;
import softtest.ast.c.ASTInclusiveORExpression;
import softtest.ast.c.ASTInitDeclarator;
import softtest.ast.c.ASTInitDeclaratorList;
import softtest.ast.c.ASTInitializer;
import softtest.ast.c.ASTInitializerList;
import softtest.ast.c.ASTIterationStatement;
import softtest.ast.c.ASTJumpStatement;
import softtest.ast.c.ASTLabelDeclaration;
import softtest.ast.c.ASTLabelDeclarationList;
import softtest.ast.c.ASTLabelDeclarator;
import softtest.ast.c.ASTLabelDeclaratorList;
import softtest.ast.c.ASTLabelType;
import softtest.ast.c.ASTLabeledStatement;
import softtest.ast.c.ASTLogicalANDExpression;
import softtest.ast.c.ASTLogicalORExpression;
import softtest.ast.c.ASTMultiplicativeExpression;
import softtest.ast.c.ASTNestedFunctionDeclaration;
import softtest.ast.c.ASTNestedFunctionDefinition;
import softtest.ast.c.ASTPRAGMA;
import softtest.ast.c.ASTParameterDeclaration;
import softtest.ast.c.ASTParameterList;
import softtest.ast.c.ASTParameterTypeList;
import softtest.ast.c.ASTPointer;
import softtest.ast.c.ASTPostfixExpression;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.ASTRelationalExpression;
import softtest.ast.c.ASTSelectionStatement;
import softtest.ast.c.ASTShiftExpression;
import softtest.ast.c.ASTSpecifierQualifierList;
import softtest.ast.c.ASTStatement;
import softtest.ast.c.ASTStatementList;
import softtest.ast.c.ASTStorageClassSpecifier;
import softtest.ast.c.ASTStructDeclaration;
import softtest.ast.c.ASTStructDeclarationList;
import softtest.ast.c.ASTStructDeclarator;
import softtest.ast.c.ASTStructDeclaratorList;
import softtest.ast.c.ASTStructOrUnion;
import softtest.ast.c.ASTStructOrUnionSpecifier;
import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.ASTTypeName;
import softtest.ast.c.ASTTypeQualifier;
import softtest.ast.c.ASTTypeQualifierList;
import softtest.ast.c.ASTTypeSpecifier;
import softtest.ast.c.ASTTypedefName;
import softtest.ast.c.ASTTypeofDeclarationSpecifier;
import softtest.ast.c.ASTUnaryExpression;
import softtest.ast.c.ASTUnaryOperator;
import softtest.ast.c.CParserVisitor;
import softtest.ast.c.CParserVisitorAdapter;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.Graph;
import softtest.dscvp.c.NameOccurrenceHashtableVisitor;
import softtest.interpro.c.Method;

public class SCVPPrintVisitor  extends CParserVisitorAdapter {
	@Override
	public Object visit(ASTFunctionDefinition node, Object data)
	{
		Graph g = node.getGraph();
		if (g == null) {
			return null;
		}
		try {
			Method m = node.getDecl().getMethod();
			String filename="e:\\graduate\\scvp_test\\uucp\\"+m.toString()+"_scvp.txt";
			FileWriter fw = new FileWriter(filename,true);
			
			g.numberOrderVisit(new SCVPDumpVisitor(), fw);
			
			fw.append("前置摘要:\n");
			fw.append(m.getCallerInfo().toString()+"\n");
			
			fw.append("前置摘要数量:");
			fw.append(m.getCallerInfo().size()+"\n");
			
			fw.append("后置摘要:\n");
			fw.append(m.getExternalEffects().toString()+"\n");
			
			fw.append("后置摘要数量:");
			fw.append(m.getExternalEffects().size()+"\n");
			
			fw.append("返回值:\n");
			fw.append(m.getReturnList().toString()+"\n");
			
			fw.append("返回值数量:");
			fw.append(m.getReturnList().size()+"\n");
			fw.close();
		} catch (Exception e) {
			e.printStackTrace();
		}

		return null;
	}
}
