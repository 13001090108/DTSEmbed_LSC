package softtest.symboltable.c;
import java.util.*;
public class Search {  
    public static NameDeclaration searchInAllUpward(String image, Scope scope) {
    	Map names=null;
    	NameDeclaration decl =null;
    	if(image==null){
    		return null;
    	}
    	names=scope.getClassDeclarations();
    	decl=searchNames(image,names);
    	if(decl==null){
    		names=scope.getVariableDeclarations();
    		decl=searchNames(image,names);
    	}
    	if(decl==null){
    		names=scope.getMethodDeclarations();
    		decl=searchNames(image,names);
    	}
    	if(decl==null&&scope.getParent()!=null){
    		decl=searchInAllUpward(image,scope.getParent());
    	}
    	return decl;
    }
    
    public static NameDeclaration searchInVariableAndMethodUpward(String image, Scope scope) {
    	Map names=null;
    	NameDeclaration decl =null;
    	if(image==null){
    		return null;
    	}
    	names=scope.getVariableDeclarations();
    	decl=searchNames(image,names);
    	if(decl==null){
    		names=scope.getMethodDeclarations();
    		decl=searchNames(image,names);
    	}
    	if(decl==null&&scope.getParent()!=null){
    		decl=searchInVariableAndMethodUpward(image,scope.getParent());
    	}
    	return decl;
    }
    
    public static NameDeclaration searchInVariableUpward(String image, Scope scope) {
    	Map names=null;
    	NameDeclaration decl =null;
    	if(image==null){
    		return null;
    	}
    	names=scope.getVariableDeclarations();
    	decl=searchNames(image,names);
    	
    	if(decl==null&&scope.getParent()!=null){
    		decl=searchInVariableUpward(image,scope.getParent());
    	}
    	return decl;
    }
    
    public static NameDeclaration searchInClassUpward(String image, Scope scope) {
    	Map names=null;
    	NameDeclaration decl =null;
    	if(image==null){
    		return null;
    	}
    	names=scope.getClassDeclarations();
    	decl=searchNames(image,names);
    	
    	if(decl==null&&scope.getParent()!=null){
    		decl=searchInClassUpward(image,scope.getParent());
    	}
    	return decl;
    }
    
    public static NameDeclaration searchInMethodUpward(String image, Scope scope) {
    	Map names=null;
    	NameDeclaration decl =null;
    	if(image==null){
    		return null;
    	}
    	names=scope.getMethodDeclarations();
    	decl=searchNames(image,names);
    	if(decl==null&&scope.getParent()!=null){
    		decl=searchInMethodUpward(image,scope.getParent());
    	}
    	return decl;
    }
    
    public static  NameDeclaration searchNames(String image,Map names){
    	NameDeclaration decl=null;
    	if(names!=null && names.size()>0){
    		Iterator i=names.keySet().iterator();
    		while(i.hasNext()){
    			NameDeclaration decl0=(NameDeclaration)i.next();
    			if(image.equals(decl0.getImage())){
    				decl=decl0;
    				if(decl.getType()!=null)
    				{
    					return decl;
    				}
    			}
    		}
    	}
    	return decl;
    }
}
