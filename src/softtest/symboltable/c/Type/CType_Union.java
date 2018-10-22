package softtest.symboltable.c.Type;

import softtest.symboltable.c.ClassNameDeclaration;
import softtest.symboltable.c.Scope;
import softtest.symboltable.c.Search;
import softtest.symboltable.c.VariableNameDeclaration;

public class CType_Union extends CType {

	private int size = -1;
	
	public CType_Union(String name) {
		super(name);
	}
	
	public void calClassSize(Scope declscope) {
		if(declscope!=null){
			int tsize=0;
			ClassNameDeclaration typedecl=(ClassNameDeclaration)Search.searchInClassUpward(getName(), declscope);
			if(typedecl!=null){
				Scope s=typedecl.getNode().getScope();
				for(Object o:s.getVariableDeclarations().keySet()){
					VariableNameDeclaration field=(VariableNameDeclaration)o;
					int fsize=field.getType().getSize();
					//¼ÓÈëpack
					int pack = softtest.config.c.Config.PACK_SIZE;
					if (pack > 8) {
						pack = 8;
					}
					if (fsize % pack != 0) {
						fsize = fsize + (pack - fsize%pack);
					}
					//tsize+=fsize;
					if(tsize<fsize){
						tsize=fsize;
					}
				}
			}
			size=tsize;
		}
	}
	
	@Override
	public int getSize() {
		return size;
	}

	public void setSize(int size) {
		this.size = size;
	}

	@Override
	public String toString() {
		return "union " + name;
	}
}
