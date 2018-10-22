/**
 * BSD-style license; for more info see http://pmd.sourceforge.net/license.html
 */
package softtest.symboltable.c;

public class ImageFinderFunction implements UnaryFunction {

	private String image;
	private NameDeclaration decl;

	public ImageFinderFunction(String image) {
		this.image = image;
	}

	public void applyTo(Object o) {
		NameDeclaration nameDeclaration = (NameDeclaration) o;
		if (image.equals(nameDeclaration.getImage())) {
			decl = nameDeclaration;
		}
	}

	public NameDeclaration getDecl() {
		return this.decl;
	}
}
