package softtest.symboltable.c;

import java.io.Serializable;

import softtest.ast.c.*;

public class ClassNameDeclaration extends AbstractNameDeclaration implements Serializable{

	public ClassNameDeclaration(ASTStructOrUnionSpecifier node) {
		super(node);
		node.setDecl(this);
	}

	public ClassNameDeclaration(ASTEnumSpecifier node) {
		super(node);
		node.setDecl(this);
	}

	public ClassNameDeclaration(ASTDirectDeclarator node) {
		super(node);
		node.setDecl(this);
	}

}
