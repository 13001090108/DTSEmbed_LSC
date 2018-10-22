package softtest.summary.lib.c;

import java.io.StringReader;
import java.util.Set;

import softtest.ast.c.ASTTranslationUnit;
import softtest.ast.c.CCharStream;
import softtest.ast.c.CParser;
import softtest.ast.c.ParseException;
import softtest.ast.c.SimpleNode;
import softtest.interpro.c.InterContext;
import softtest.summary.c.MethodFeatureType;
import softtest.summary.c.MethodSummary;
import softtest.summary.gcc.fault.MethodRMFeature;
import softtest.symboltable.c.MethodNameDeclaration;
import softtest.symboltable.c.ScopeAndDeclarationFinder;
import softtest.symboltable.c.SourceFileScope;


public class LibMethodDespRm extends LibMethodDesp {

	public LibMethodDespRm(MethodFeatureType type, Object value) {
		super(type, value);
	}

	@Override
	public void createFeature(String libName, SimpleNode node, MethodSummary mtSummary) {
		MethodRMFeature rmFeature = new MethodRMFeature();
		CParser parser = CParser.getParser(new CCharStream(new StringReader((String)value)));
		ASTTranslationUnit root=null;
		try {
			root = parser.TranslationUnit();
		} catch (ParseException e) {
			e.printStackTrace();
		}
		ScopeAndDeclarationFinder sc = new ScopeAndDeclarationFinder();
		root.jjtAccept(sc, null);
		SourceFileScope scope = (SourceFileScope)root.getScope();
		Set<MethodNameDeclaration>methods = scope.getMethodDeclarations().keySet();
		if (methods != null && methods.size() > 0) {
			MethodNameDeclaration temp = methods.iterator().next();
			temp.setNode(null);
			temp.setScope(null);
			rmFeature.setReleaseMethod(temp);
			InterContext interContext = InterContext.getInstance();
			interContext.addLibMethodDecl(methods);
		}
		mtSummary.addSideEffect(rmFeature);
	}
	

}
