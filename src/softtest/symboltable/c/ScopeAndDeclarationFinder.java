package softtest.symboltable.c;

import softtest.ast.c.*;
import softtest.domain.c.interval.PointerValue;
import softtest.config.c.*;
import softtest.interpro.c.InterContext;
import softtest.interpro.c.ScopeType;
import softtest.interpro.c.Variable;
import softtest.symboltable.c.Type.*;

import java.util.*;


public class ScopeAndDeclarationFinder extends CParserVisitorAdapter
{
	private Stack<Scope> scopes = new Stack<Scope>();
	
	private Stack<CType> typecontex=new Stack<CType>();
	
	private int NoNameTypeCount = 0;
	
	private int paramIndex = 0;
	
	private Hashtable<String,CType_Struct> strs=new Hashtable<String,CType_Struct>();
	
	private Hashtable<String,Integer> enums=new Hashtable<String,Integer>();

	private void addScope(Scope newScope, SimpleNode node){
		if(!scopes.isEmpty()){
			newScope.setParent((Scope) scopes.peek());
		}
		scopes.push(newScope);
		node.setScope(newScope);
	}

	private void createLocalScope(SimpleNode node){
		addScope(new LocalScope(node), node);
	}

	private void createMethodScope(SimpleNode node){
		addScope(new MethodScope(node), node);
	}

	private void createClassScope(SimpleNode node, String name) {
		addScope(new ClassScope(name, node), node);
	}

	private void createSourceFileScope(SimpleNode node) {
		addScope(new SourceFileScope(node), node);
	}

	public Object visit(ASTTranslationUnit node, Object data) {
		createSourceFileScope(node);
		cont(node, data);
		return data;
	}
	
	//add by zhouhb
	//2011.5.5
	//实现了结构体成员的嵌套声明
	private void structMemDeclaration(String image,CType type,Scope scope,String filename,ASTDeclarator node,int level){
		//dongyk 20140605 控制域敏感分析时多级变量的层数
		if(level>Config.VAR_LEVEL)
			return;
		
		NameDeclaration fDecl=Search.searchInVariableAndMethodUpward(image, scope);
		VariableNameDeclaration fatherDecl=null;
		if(fDecl!=null){
			fatherDecl =(VariableNameDeclaration)fDecl;
		}
		if(type instanceof CType_Struct){
			for(String mem:((CType_Struct)type).getfieldType().keySet()){
				CType memType=((CType_Struct)type).getfieldType().get(mem);
				if(memType instanceof CType_Struct || memType instanceof CType_Pointer&&((CType_Pointer)memType).getOriginaltype() instanceof CType_Struct){
					VariableNameDeclaration decl = new VariableNameDeclaration(filename,scope,image+"."+mem,node);
					decl.setType(memType);
					decl.setGen(true);
					setInitializedVariable(decl);
					scope.addDeclaration(decl);
					addToParent(decl, image);
					node.decl.add(decl);
					decl.setFatherVariable(fatherDecl);
					structMemDeclaration(image+"."+mem,((CType_Struct)type).getfieldType().get(mem),scope,filename,node,level+1);
				}else{
					VariableNameDeclaration decl = new VariableNameDeclaration(filename,scope,image+"."+mem,node);
//					if(memType instanceof CType_Pointer){
//						pointersDeclaration((CType_Pointer)memType,scope,filename,node,decl.getImage());
//					}
					decl.setType(memType);
					decl.setGen(true);
					setInitializedVariable(decl);
					scope.addDeclaration(decl);
					node.decl.add(decl);
					decl.setFatherVariable(fatherDecl);
				}
			}
		}else if(type instanceof CType_Pointer&&((CType_Pointer)type).getDeepOriginaltype() instanceof CType_Struct){
			CType_Struct str=(CType_Struct)((CType_Pointer)type).getDeepOriginaltype();
			for(String mem:str.getfieldType().keySet()){
				if(str.getfieldType().get(mem) instanceof CType_Struct){
					VariableNameDeclaration decl = new VariableNameDeclaration(filename,scope,image+"->"+mem,node);
					decl.setType(str.getfieldType().get(mem));
					decl.setGen(true);
					setInitializedVariable(decl);
					scope.addDeclaration(decl);
					node.decl.add(decl);
					decl.setFatherVariable(fatherDecl);
					structMemDeclaration(image+"->"+mem,(CType_Struct)str.getfieldType().get(mem),scope,filename,node,level+1);
				}else{
					VariableNameDeclaration decl = new VariableNameDeclaration(filename,scope,image+"->"+mem,node);
					decl.setType(str.getfieldType().get(mem));
					decl.setGen(true);
					setInitializedVariable(decl);
					scope.addDeclaration(decl);
					node.decl.add(decl);
					decl.setFatherVariable(fatherDecl);
				}
			}
		}
	}
	//实现了多级指针的独立成员声明
	//2011.5.17
	private void pointersDeclaration(CType_Pointer ptype,Scope scope,String filename,ASTDeclarator node,String name,int level){
		//dongyk 20140605 控制域敏感分析时多级变量的层数
		if(level>Config.VAR_LEVEL)
			return;
		
		int rank=ptype.getRank();
		CType type=ptype.getOriginaltype();
		while(type instanceof CType_Pointer){
			VariableNameDeclaration decl = new VariableNameDeclaration(filename,scope,getP(rank-((CType_Pointer)type).getRank(),"*")+name,node);
			decl.setType(type);
			decl.setGen(true);
			setInitializedVariable(decl);
			scope.addDeclaration(decl);
			node.decl.add(decl);
			type=((CType_Pointer)type).getOriginaltype();
		}
		VariableNameDeclaration decl = new VariableNameDeclaration(filename,scope,getP(rank,"*")+name,node);
		decl.setType(type);
		decl.setGen(true);
		setInitializedVariable(decl);
		scope.addDeclaration(decl);
		node.decl.add(decl);
	}
	
	//实现了数组成员的独立成员声明
	//2011.5.19
	private void arrayMemDeclaration(String image,CType_Array atype,Scope scope,String filename,ASTDeclarator node,int level){
		//dongyk 20140605 控制域敏感分析时多级变量的层数
		if(level>Config.VAR_LEVEL)
			return;
		
		NameDeclaration fDecl=Search.searchInVariableAndMethodUpward(image, scope);
		VariableNameDeclaration fatherDecl=null;
		if(fDecl!=null){
			fatherDecl =(VariableNameDeclaration)fDecl;
		}
		if(atype.getOriginaltype() instanceof CType_Array){
			for(int i=0;i<atype.getDimSize();i++){
				/*dongyk 20120411*/
				/*识别所有维数的指针，例如定义了int a[2][2]，共有a、a[0]、a[1]、a[0][0]、a[0][1]、a[1][0]、a[1][1]共7个变量*/
				VariableNameDeclaration decl = new VariableNameDeclaration(filename,scope,image+"["+i+"]",node);
				decl.setType(atype.getOriginaltype());
				decl.setGen(true);
				setInitializedVariable(decl);
				scope.addDeclaration(decl);
				node.decl.add(decl);
				decl.setFatherVariable(fatherDecl);
				CType originType=(CType_Array)atype.getOriginaltype();	
				if(originType instanceof CType_Array && ((CType_Array)atype).getMemNum()<=Config.MaxArray)
				{
					arrayMemDeclaration(image+"["+i+"]",(CType_Array)originType,scope,filename,node,level+1);
				}
			}
		}else if(atype.getOriginaltype() instanceof CType_Struct){
			for(int i=0;i<atype.getDimSize();i++){
				/*dongyk 20120411*/
				/*识别所有维数的指针*/
				VariableNameDeclaration decl = new VariableNameDeclaration(filename,scope,image+"["+i+"]",node);
				decl.setType(atype.getOriginaltype());
				decl.setGen(true);
				setInitializedVariable(decl);
				scope.addDeclaration(decl);
				node.decl.add(decl);
				decl.setFatherVariable(fatherDecl);							
				structMemDeclaration(image+"["+i+"]",atype.getOriginaltype(),scope,filename,node,level+1);
			}
		}else{
			for(int i=0;i<atype.getDimSize();i++){
				VariableNameDeclaration decl = new VariableNameDeclaration(filename,scope,image+"["+i+"]",node);
				decl.setType(atype.getOriginaltype());
				decl.setGen(true);
				setInitializedVariable(decl);
				scope.addDeclaration(decl);
				node.decl.add(decl);
				decl.setFatherVariable(fatherDecl);
			}
		}
	}
	
	
	private String getP(int num,String s){
		StringBuffer re=new StringBuffer();
		for(int i=0;i<num;i++){
			re.append(s);
		}
		return re.toString();
	}
	//end by zhouhb

	public Object visit(ASTStructOrUnionSpecifier node, Object data)
	{		
		Scope s = ((SimpleNode) node.jjtGetParent()).getScope(); 
		String name=node.getImage();
		ASTStructOrUnion child = (ASTStructOrUnion) node.getFirstDirectChildOfType(ASTStructOrUnion.class);
		CType type = s.getType(name);

		if(name.equals("")){
			name = "NoName_" + NoNameTypeCount++;
			node.setImage(name);
		}
		
		if (child != null) {
			if (type == null) {
				if (child.getImage().equals("struct")) {
					type = new CType_Struct(name);
					s.addType(type.toString(), type);					
				} else {
					type = new CType_Union(name);
					s.addType(type.toString(), type);
				}
			}
			node.setType(type);
		}

		if (node.jjtGetNumChildren() < 2) {
			super.visit(node, data);
			//add by zhouhb
			if(Config.Field){
				for(String n:strs.keySet()){
					if(name.equals(n)){
						type=strs.get(n);
						node.setType(type);
					}
				}
			}
		} else {
			createClassScope(node, name);
			cont(node, data);
		}

		if (node.jjtGetNumChildren() >= 2) {
			ClassNameDeclaration decl = new ClassNameDeclaration(node);
			s.addDeclaration(decl);
			type.calClassSize(s);
			decl.setType(type);
			//add by zhouhb
			if(type instanceof CType_Struct){
				strs.put(name, (CType_Struct)type);
			}
		}
		return data;
	}

	public Object visit(ASTEnumSpecifier node, Object data) {

		Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
		String name = node.getImage();
		if (name.equals("")) {
			name = "NoName_" + NoNameTypeCount++;
			node.setImage(name);
		}

		if (node.jjtGetNumChildren() < 1) {
			super.visit(node, data);// 这种情况就多余了吧？
		} else {
			createClassScope(node, name);
			cont(node, data);
		}

		CType type = s.getType(name);
		if (type == null) {
			type = new CType_Enum(name);
			//add by zhouhb
			//增加enum枚举值数量的识别
			//2011.12.21
			if(node.jjtGetNumChildren()!=0){
				((CType_Enum)type).setValue(node.jjtGetChild(0).jjtGetNumChildren());
				enums.put(type.getName(),node.jjtGetChild(0).jjtGetNumChildren());
			}else{
				for(String n:enums.keySet()){
					if(type.getName().equals(n)){
						((CType_Enum)type).setValue(enums.get(n));
						node.setType(type);
					}
				}
			}
			//end by zhouhb
			s.addType(type.toString(), type);
		}
		node.setType(type);

		if (node.jjtGetNumChildren() >= 1) {
			ClassNameDeclaration decl = new ClassNameDeclaration(node);
			s.addDeclaration(decl);
			decl.setType(type);
		}
		return data;
	}

	public Object visit(ASTEnumerator node, Object data) {
		VariableNameDeclaration decl = new VariableNameDeclaration(node);
		CType type = CType_BaseType.getBaseType("int");
		decl.setType(type);
		node.setType(type);
		Scope s = ((SimpleNode) node.jjtGetParent()).getScope().getParent();
		s.addDeclaration(decl);
		return data;
	}

	public Object visit(ASTCompoundStatement node, Object data) {
		createLocalScope(node);
		cont(node, data);
		return data;
	}

	public Object visit(ASTNestedFunctionDeclaration node, Object data) {
		createMethodScope(node);
		if (node.jjtGetNumChildren() > 0
				&& node.jjtGetChild(0) instanceof ASTDeclarationSpecifiers) {
			ASTDeclarationSpecifiers ds = (ASTDeclarationSpecifiers) node
					.jjtGetChild(0);
			ds.jjtAccept(this, data);
			typecontex.push(ds.getType());
			for (int i = 1; i < node.jjtGetNumChildren(); ++i) {
				node.jjtGetChild(i).jjtAccept(this, data);
			}
		} else {
			typecontex.push(CType_BaseType.getBaseType("int"));
			super.visit(node, data);
		}
		scopes.pop();

		Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
		MethodNameDeclaration decl = new MethodNameDeclaration(node);
		s.addDeclaration(decl);

		ASTParameterTypeList paramtypelist = null;
		CType type = null;
		ArrayList<String> oplist = node.getOperatorType();
		ArrayList<Boolean> flaglist = node.getFlags();
		int j = node.getFirstSlot();
		for (int i = 0; i < flaglist.size(); i++) {
			if (oplist.get(i).equals("")) {
				if (flaglist.get(i)) {
					ASTDeclarator d = (ASTDeclarator) node.jjtGetChild(j++);
					type = d.getType();
				}
			} else if (oplist.get(i).equals("(")) {
				CType_Function ftype = new CType_Function();
				CType.setOrignType(type, ftype);
				if (flaglist.get(i)) {
					ASTParameterTypeList d = (ASTParameterTypeList) node
							.jjtGetChild(j++);
					if (d != null && d.getType() instanceof CType_Function) {
						ftype.setArgTypes(((CType_Function) d.getType())
								.getArgTypes());
					}
				}
			}
		}
		paramtypelist = (ASTParameterTypeList) node
				.getFirstDirectChildOfType(ASTParameterTypeList.class);

		if (paramtypelist != null
				&& paramtypelist.getType() instanceof CType_Function) {
			type = (CType_Function) paramtypelist.getType();
		} else {
			type = new CType_Function();
		}

		CType.setOrignType(type, typecontex.peek());
		type.setName(node.getImage());

		typecontex.pop();

		node.setType(type);
		decl.setType(type);
		decl.setImage(node.getImage());
		return data;
	}

	public Object visit(ASTFunctionDeclaration node, Object data){
		//ZYS:针对函数声明，无需生成MethodScope
		//createMethodScope(node);
		if(node.jjtGetNumChildren()>0&&node.jjtGetChild(0)instanceof ASTDeclarationSpecifiers){
			ASTDeclarationSpecifiers ds=(ASTDeclarationSpecifiers)node.jjtGetChild(0);
			ds.jjtAccept(this, data);
			typecontex.push(ds.getType());
			for (int i = 1; i < node.jjtGetNumChildren(); ++i) {
				node.jjtGetChild(i).jjtAccept(this, data);
			}
		} else {
			typecontex.push(CType_BaseType.getBaseType("int"));
			super.visit(node, data);
		}
		// scopes.pop();

		ASTParameterTypeList paramtypelist = null;
		CType type = null;

		ArrayList<String> oplist = node.getOperatorType();
		ArrayList<Boolean> flaglist = node.getFlags();
		int j = node.getFirstSlot();
		for (int i = 0; i < flaglist.size(); i++) {
			if (oplist.get(i).equals("")) {
				if (flaglist.get(i)) {
					ASTDeclarator d = (ASTDeclarator) node.jjtGetChild(j++);
					type = d.getType();
				}
			} else if (oplist.get(i).equals("(")) {
				CType_Function ftype = new CType_Function();
				if (type != null) {
					CType.setOrignType(type, ftype);
				} else {
					type = ftype;
				}
				if (flaglist.get(i)) {
					if(node.jjtGetChild(j) instanceof ASTIdentifierList){
						ASTIdentifierList d = (ASTIdentifierList) node.jjtGetChild(j++);
						if (d != null && d.getType() instanceof CType_Function) {
							ftype.setArgTypes(((CType_Function) d.getType()).getArgTypes());
							ftype.setIsVarArg(((CType_Function) d.getType()).isVarArg());
						}
					}else if(node.jjtGetChild(j) instanceof ASTParameterTypeList){
						ASTParameterTypeList d = (ASTParameterTypeList) node.jjtGetChild(j++);
						if (d != null && d.getType() instanceof CType_Function) {
							ftype.setArgTypes(((CType_Function) d.getType()).getArgTypes());
							ftype.setIsVarArg(((CType_Function) d.getType()).isVarArg());
						}
					}	
				}
			}
		}
		if (type == null) {
			paramtypelist = (ASTParameterTypeList) node.getFirstDirectChildOfType(ASTParameterTypeList.class);
			if (paramtypelist != null&&paramtypelist.getType()instanceof CType_Function) {
				type = (CType_Function) paramtypelist.getType();
			} else {
				type = new CType_Function();
			}
		}
		ASTPointer pointer = (ASTPointer) node.getFirstDirectChildOfType(ASTPointer.class);
		if (pointer != null) {
			CType ptype = pointer.getType();
			CType.setOrignType(type, ptype);
		}

		type.setName(node.getImage());
		CType.setOrignType(type, typecontex.peek());
		typecontex.pop();

		node.setType(type);

		// zys:在调用MethodNameDeclaration在toString时显示完整的函数名称
		Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
		
		//zys 2011.6.22	对于函数内的函数声明f(){void g();}，将g的声明放到文件作用域中，当访问其定义节点时再进行更新
		while(!(s instanceof SourceFileScope)){
			s=s.getParent();
		}
		
		//zys:2010.6.8 如果是函数声明节点，则首先判断是否是库函数，并获取其摘要信息
		InterContext context=InterContext.getInstance();
		Map<String, MethodNameDeclaration> set=context.getLibMethodDecls();
		if(set.size()>0)
		{
			MethodNameDeclaration mnd=set.get(node.getImage());
			if(mnd!=null){
				if(node.getFileName()!=null)
					mnd.setFileName(node.getFileName());
				mnd.setNode(node);
				mnd.setScope(s);
				s.addDeclaration(mnd);
				return data;
			}
		}
		MethodNameDeclaration decl = new MethodNameDeclaration(node);
		decl.setType(type);
		decl.setImage(node.getImage());
		s.addDeclaration(decl);
		return data;
	}

	public Object visit(ASTNestedFunctionDefinition node, Object data) {
		Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
		MethodNameDeclaration decl = new MethodNameDeclaration(node);
		s.addDeclaration(decl);
		createMethodScope(node);

		ASTDeclarationSpecifiers ds = (ASTDeclarationSpecifiers) node
				.jjtGetChild(0);
		ds.jjtAccept(this, data);
		typecontex.push(ds.getType());
		for (int i = 1; i < node.jjtGetNumChildren(); ++i) {
			node.jjtGetChild(i).jjtAccept(this, data);
		}
		scopes.pop();

		ASTDeclarator declarator = (ASTDeclarator) node
				.getFirstDirectChildOfType(ASTDeclarator.class);
		if (declarator == null) {
			throw new RuntimeException(
					"AST tree error,FunctionDefinition must have a Declarator!");
		}
		ASTDirectDeclarator de = (ASTDirectDeclarator) declarator
				.getFinalDirectDeclarator();
		ASTParameterTypeList paramtypelist = (ASTParameterTypeList) de
				.getFirstDirectChildOfType(ASTParameterTypeList.class);
		ASTIdentifierList identifierlist = (ASTIdentifierList) de
				.getFirstDirectChildOfType(ASTIdentifierList.class);
		CType_Function type = null;
		if (paramtypelist != null
				&& paramtypelist.getType() instanceof CType_Function) {
			type = (CType_Function) paramtypelist.getType();
		} else {
			// //gcc:f(i)int i;{} f(){} keilc:f(){}
			type = new CType_Function();
		}
		ASTDeclarationList dl = (ASTDeclarationList) node
				.getFirstDirectChildOfType(ASTDeclarationList.class);
		if (dl != null) {
			List<String> identifiers = null;
			if (identifierlist != null) {
				identifiers = identifierlist.getIdentifiers();
			} else {
				throw new RuntimeException(
						"AST tree error,DeclarationList use error!");
			}
			ArrayList<CType> typelist = new ArrayList<CType>();
			for (String identifier : identifiers) {
				NameDeclaration namedecl = Search.searchNames(identifier, node
						.getScope().getVariableDeclarations());
				if (namedecl == null) {
					throw new RuntimeException(
							"AST tree error,DeclarationList use error!");
				}
				typelist.add(namedecl.getType());
			}
			type.setArgTypes(typelist);
		}
		CType.setOrignType(type, typecontex.peek());
		type.setName(node.getImage());

		typecontex.pop();

		node.setType(type);
		decl.setType(type);
		decl.setImage(node.getImage());
		return data;
	}

	public Object visit(ASTFunctionDefinition node, Object data) {
		paramIndex = 0;
		Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
		MethodNameDeclaration decl = new MethodNameDeclaration(node);
		s.addDeclaration(decl);
		createMethodScope(node);
		if (node.jjtGetChild(0) instanceof ASTDeclarationSpecifiers) {
			ASTDeclarationSpecifiers ds = (ASTDeclarationSpecifiers) node
					.jjtGetChild(0);
			ds.jjtAccept(this, data);
			typecontex.push(ds.getType());
			for (int i = 1; i < node.jjtGetNumChildren(); ++i) {
				node.jjtGetChild(i).jjtAccept(this, data);
			}
		} else {
			typecontex.push(CType_BaseType.getBaseType("int"));
			super.visit(node, data);
		}
		scopes.pop();

		ASTDeclarator declarator = (ASTDeclarator) node
				.getFirstDirectChildOfType(ASTDeclarator.class);
		if (declarator == null) {
			throw new RuntimeException(
					"AST tree error,FunctionDefinition must have a Declarator!");
		}
		ASTDirectDeclarator de = (ASTDirectDeclarator) declarator
				.getFinalDirectDeclarator();
		ASTParameterTypeList paramtypelist = (ASTParameterTypeList) de
				.getFirstDirectChildOfType(ASTParameterTypeList.class);
		ASTIdentifierList identifierlist = (ASTIdentifierList) de
				.getFirstDirectChildOfType(ASTIdentifierList.class);
		//liuli增加对可变参数的处理
		if(identifierlist == null){
			identifierlist = (ASTIdentifierList) declarator
			.getFirstChildOfType(ASTIdentifierList.class);
		}
		CType_Function type = null;

		if (declarator.getType() instanceof CType_Function) {
			type = (CType_Function) declarator.getType();
		} else {
			type = new CType_Function();
		}
		ASTDeclarationList dl = (ASTDeclarationList) node
				.getFirstDirectChildOfType(ASTDeclarationList.class);
		if (dl != null) {
			List<String> identifiers = null;
			if (paramtypelist != null) {
				ASTParameterList paramlist = (ASTParameterList) paramtypelist
						.getFirstDirectChildOfType(ASTParameterList.class);
				if (paramlist == null) {
					throw new RuntimeException(
							"AST tree error,ParameterTypeList must have a ParameterList!");
				}
				identifiers = paramlist.getIdentifiers();
			} else if (identifierlist != null) {
				identifiers = identifierlist.getIdentifiers();
			} else {
				throw new RuntimeException(
						"AST tree error,DeclarationList use error!");
			}
			ArrayList<CType> typelist = new ArrayList<CType>();
			for (String identifier : identifiers) {
				NameDeclaration namedecl = Search.searchNames(identifier, node
						.getScope().getVariableDeclarations());
				if (namedecl == null && identifiers.indexOf(identifier)==0) {
					typelist.add(new CType_BaseType("char"));
					//throw new RuntimeException("DeclarationList use error!");
				}
				if(namedecl != null){
					typelist.add(namedecl.getType());
				}
			}
			type.setArgTypes(typelist);
		}

		CType.setOrignType(type, typecontex.peek());
		type.setName(node.getImage());

		typecontex.pop();

		node.setType(type);
		decl.setType(type);
		decl.setImage(node.getImage());
                                                   
		// zys:如果在函数定义之前已经对函数进行了声明，则更新函数声明信息
		Map<MethodNameDeclaration, ArrayList<NameOccurrence>> methods = ((SourceFileScope) s)
				.getMethodDeclarations();
		for (MethodNameDeclaration method : methods.keySet()) {
			if (method.getImage().equals(decl.getImage())) {
				ArrayList<NameOccurrence> occs = methods.get(method);
				methods.remove(method);
				methods.put(decl, occs);
				break;
			}
		}
		return data;
	}

	public Object visit(ASTIterationStatement node, Object data) {
		createLocalScope(node);
		cont(node, data);
		return data;
	}

	public Object visit(ASTParameterTypeList node, Object data) {
		super.visit(node, data);
		CType_Function type = null;
		type = (CType_Function) ((ASTParameterList) node.jjtGetChild(0))
				.getType();
		type.setIsVarArg(node.isVararg());
		if (type.getArgTypes().size() == 1
				&& type.getArgTypes().get(0).equals(
						CType_BaseType.getBaseType("void"))) {
			type = null;
		}
		node.setType(type);
		return data;
	}

	public Object visit(ASTIdentifierList node, Object data) {
		super.visit(node, data);
		CType_Function type = new CType_Function();
		for (int i = 0; i < node.getIdentifiers().size(); i++) {
				type.addArgType(CType_BaseType.getBaseType("int"));
		}
		node.setType(type);
		return data;
	}

	public Object visit(ASTParameterList node, Object data) {
		super.visit(node, data);
		CType_Function type = new CType_Function();
		for (int i = 0; i < node.jjtGetNumChildren(); i++) {
			type.addArgType(((ASTParameterDeclaration) node.jjtGetChild(i))
					.getType());
		}
		node.setType(type);
		return data;
	}

	public Object visit(ASTParameterDeclaration node, Object data) {
		if (node.jjtGetNumChildren() > 0
				&& node.jjtGetChild(0) instanceof ASTDeclarationSpecifiers) {
			ASTDeclarationSpecifiers ds = (ASTDeclarationSpecifiers) node
					.jjtGetChild(0);
			ds.jjtAccept(this, data);
			typecontex.push(ds.getType());
			for (int i = 1; i < node.jjtGetNumChildren(); ++i) {
				node.jjtGetChild(i).jjtAccept(this, data);
			}
		} else {
			typecontex.push(CType_BaseType.getBaseType("int"));
			super.visit(node, data);
		}

		CType type = null, dtype = null;
		type = typecontex.peek();
		ASTDeclarator de = (ASTDeclarator) node
				.getFirstDirectChildOfType(ASTDeclarator.class);
		ASTAbstractDeclarator ad = (ASTAbstractDeclarator) node
				.getFirstDirectChildOfType(ASTAbstractDeclarator.class);

		if (de != null) {
			dtype = de.getType();
		}
		if (ad != null) {
			dtype = ad.getType();
		}
		if (dtype != null) {
			CType.setOrignType(dtype, type);
			type = dtype;
		}
		node.setType(type);

		if (de != null) {
			de.setType(type);
			ASTDirectDeclarator temp = de.getFinalDirectDeclarator();
			if (temp.getDecl() != null) {
				VariableNameDeclaration decl=(VariableNameDeclaration)temp.getDecl();
				decl.setType(type);
				if(Config.Field){
					if(decl.getType()instanceof CType_Struct||((decl.getType()instanceof CType_Pointer&&((CType_Pointer)decl.getType()).getDeepOriginaltype()instanceof CType_Struct))){
						structMemDeclaration(de.getImage(),type,node.getScope(),node.getFileName(),de,0);
						if(temp.getVariableNameDeclaration()!=null){
							temp.getVariableNameDeclaration().mems=de.decl;
						}
					}else if(decl.getType() instanceof CType_Typedef && ((CType_Typedef)decl.getType()).getOriginaltype() instanceof CType_Struct){
						structMemDeclaration(de.getImage(),((CType_Typedef)decl.getType()).getOriginaltype(),node.getScope(),node.getFileName(),de,0);
						if(temp.getVariableNameDeclaration()!=null){
							temp.getVariableNameDeclaration().mems=de.decl;
						}
					}
					else if(decl.getType()instanceof CType_Pointer){
						pointersDeclaration((CType_Pointer)decl.getType(),node.getScope(),node.getFileName(),de,de.getImage(),0);
					}else if(decl.getType() instanceof CType_Array && ((CType_Array)decl.getType()).getMemNum()<=Config.MaxArray){
						arrayMemDeclaration(temp.getImage(),(CType_Array)decl.getType(),node.getScope(),node.getFileName(),de,0);
					}
				}
			}
		}

		typecontex.pop();

		// 确定参数的序号
		// liuli:2010.3.24 directDec取值有可能为空
		SimpleNode parent = (SimpleNode) node.jjtGetParent();
		for (int k = 0; k < parent.jjtGetNumChildren(); k++) {
			if (parent.jjtGetChild(k) == node) {
				ASTDirectDeclarator directDec = (ASTDirectDeclarator) (node
						.getFirstChildOfType(ASTDirectDeclarator.class));
				if (directDec == null)
					return data;
				if (directDec.getVariableNameDeclaration() != null)
					directDec.getVariableNameDeclaration().setParamIndex(k);
			}
		}
		return data;
	}

	public Object visit(ASTTypeName node, Object data) {
		ASTSpecifierQualifierList ds = (ASTSpecifierQualifierList) node
				.jjtGetChild(0);
		ds.jjtAccept(this, data);
		typecontex.push(ds.getType());
		for (int i = 1; i < node.jjtGetNumChildren(); ++i) {
			node.jjtGetChild(i).jjtAccept(this, data);
		}

		CType type = null, dtype = null;
		type = typecontex.peek();
		ASTAbstractDeclarator ad = (ASTAbstractDeclarator) node
				.getFirstDirectChildOfType(ASTAbstractDeclarator.class);
		if (ad != null) {
			dtype = ad.getType();
		}
		if (dtype != null) {
			CType.setOrignType(dtype, type);
			type = dtype;
		}
		node.setType(type);
		typecontex.pop();
		return data;
	}

	public Object visit(ASTPointer node, Object data) {
		super.visit(node, data);
		CType type = new CType_Pointer();
		ASTPointer pointer = (ASTPointer) node
				.getFirstDirectChildOfType(ASTPointer.class);
		ASTTypeQualifierList qlist = (ASTTypeQualifierList) node
				.getFirstDirectChildOfType(ASTTypeQualifierList.class);
		if (qlist != null) {
			CType_Qualified qtype = new CType_Qualified(type);
			for (int i = 0; i < qlist.jjtGetNumChildren(); i++) {
				ASTTypeQualifier q = (ASTTypeQualifier) qlist.jjtGetChild(i);
				qtype.addQualifier(q.getImage());
			}
			type = qtype;
		}
		if (pointer != null) {
			CType ptype = pointer.getType();
			CType.setOrignType(ptype, type);
			type = ptype;
		}
		node.setType(type);
		return data;
	}

	public Object visit(ASTDirectAbstractDeclarator node, Object data) {
		super.visit(node, data);
		ArrayList<String> oplist = node.getOperatorType();
		ArrayList<Boolean> flaglist = node.getFlags();
		CType type = null;
		int j = 0;
		for (int i = 0; i < flaglist.size(); i++) {
			if (oplist.get(i).equals("")) {
				if (flaglist.get(i)) {
					ASTAbstractDeclarator de = (ASTAbstractDeclarator) node
							.jjtGetChild(j++);
					type = de.getType();
				}
			} else if (oplist.get(i).equals("[")) {
				boolean fixed = false;
				int size = -1;
				if (flaglist.get(i)) {
					ASTConstantExpression de = (ASTConstantExpression) node
							.jjtGetChild(j++);
					fixed = true;
					size = de.getIntegerValue();
				}
				CType_Array atype = new CType_Array();
				atype.setFixed(fixed);
				atype.setDimSize(size);
				if (type != null) {
					CType.setOrignType(type, atype);
				} else {
					type = new CType_Array();
					((CType_Array) type).setFixed(fixed);
					((CType_Array) type).setDimSize(size);
				}
			} else if (oplist.get(i).equals("(")) {
				CType_Function ftype = new CType_Function();
				if (type != null) {
					CType.setOrignType(type, ftype);
				} else {
					type = ftype;
				}
				if (flaglist.get(i)) {
					Node tempnode = node.jjtGetChild(j++);
					if (tempnode instanceof ASTParameterTypeList) {
						ASTParameterTypeList de = (ASTParameterTypeList) tempnode;
						if (de.getType() instanceof CType_Function) {
							ftype.setArgTypes(((CType_Function) de.getType())
									.getArgTypes());
							ftype.setIsVarArg(((CType_Function) de.getType())
									.isVarArg());
						}
					}
				}
			}
		}
		node.setType(type);
		return data;
	}

	public Object visit(ASTAbstractDeclarator node, Object data) {
		super.visit(node, data);
		ASTPointer pointer = (ASTPointer) node
				.getFirstDirectChildOfType(ASTPointer.class);
		ASTDirectAbstractDeclarator de = (ASTDirectAbstractDeclarator) node
				.getFirstDirectChildOfType(ASTDirectAbstractDeclarator.class);
		CType type = null;
		if (de == null) {
			if (pointer != null) {
				type = pointer.getType();
			}
		} else {
			type = de.getType();
			if (pointer != null) {
				CType ptype = pointer.getType();
				CType.setOrignType(type, ptype);
			}
		}

		node.setType(type);
		return data;
	}

	public Object visit(ASTDirectDeclarator node, Object data) {
		// liuli:更改对typedef的处理
		if (node.isIstypedef()) {
			ClassNameDeclaration decl = new ClassNameDeclaration(node);
			Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
			s.addDeclaration(decl);
			node.setDecl(decl);
		} else if (!node.isFunctionName()) {
			VariableNameDeclaration decl = new VariableNameDeclaration(node);
			Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
			s.addDeclaration(decl);
			node.setDecl(decl);
		}

		super.visit(node, data);

		CType type = null;
		ArrayList<String> oplist = node.getOperatorType();
		ArrayList<Boolean> flaglist = node.getFlags();
		int j = 0;
		for (int i = 0; i < flaglist.size(); i++) {
			if (oplist.get(i).equals("")) {
				if (flaglist.get(i)) {
					ASTDeclarator de = (ASTDeclarator) node.jjtGetChild(j++);
					type = de.getType();
				}
			}else if(oplist.get(i).equals("[")){
				boolean fixed=false;
				int size=-1;
				if(flaglist.get(i)){
					ASTConstantExpression de=(ASTConstantExpression)node.jjtGetChild(j++);
					fixed=true;
					size=de.getIntegerValue();
					
				}
				CType_Array atype = new CType_Array();
				atype.setFixed(fixed);
				atype.setDimSize(size);
				if (type != null) {
					CType.setOrignType(type, atype);
				} else {
					type = new CType_Array();
					((CType_Array) type).setFixed(fixed);
					((CType_Array) type).setDimSize(size);
				}

			} else if (oplist.get(i).equals("(")) {
				CType_Function ftype = new CType_Function();
				if (type != null) {
					CType.setOrignType(type, ftype);
				} else {
					type = ftype;
					;
				}
				if (flaglist.get(i)) {
					Node tempnode = node.jjtGetChild(j++);
					if (tempnode instanceof ASTParameterTypeList) {
						ASTParameterTypeList de = (ASTParameterTypeList) tempnode;
						if (de.getType() instanceof CType_Function) {
							ftype.setArgTypes(((CType_Function) de.getType())
									.getArgTypes());
							ftype.setIsVarArg(((CType_Function) de.getType())
									.isVarArg());
						}
					} else if (tempnode instanceof ASTIdentifierList) {
						ASTIdentifierList identifierlist = (ASTIdentifierList) tempnode;
						if (identifierlist.getType() instanceof CType_Function) {
							ftype.setArgTypes(((CType_Function) identifierlist
									.getType()).getArgTypes());
						}
					}
				}
			}
		}
		node.setType(type);

		// zys:如果为keilc中的绝对地址变量声明，则添加变量的memoryAddress属性
		node.setMemoryAddress();
		return data;
	}

	public Object visit(ASTDeclarator node, Object data) {
		super.visit(node, data);
		ASTPointer pointer = (ASTPointer) node
				.getFirstDirectChildOfType(ASTPointer.class);
		ASTDirectDeclarator de = (ASTDirectDeclarator) node
				.getFirstDirectChildOfType(ASTDirectDeclarator.class);
		CType type = null;
		if (de == null) {
			throw new RuntimeException("AST tree error,Declarator use error!");
		}
		type = de.getType();
		if (pointer != null) {
			CType ptype = pointer.getType();
			if (!CType.setOrignType(type, ptype)) {
				type = ptype;
			}
		}
		node.setType(type);
		return data;
	}

	/** zys:如果变量在声明的同时进行初始化，则将其与一个Variable关联 */
	private void setInitializedVariable(VariableNameDeclaration v) {
		CType type = v.getType();
		Scope scope = v.getScope();
		String name = v.getImage();
		Variable var = null;
		if (scope instanceof SourceFileScope) {
			var = new Variable(ScopeType.INTER_SCOPE, name, type);
		} else if (scope instanceof MethodScope) //不大清楚为什么限制v
			//else if (scope instanceof MethodScope && v.isParam())
			{
			var = new Variable(ScopeType.METHOD_SCOPE, name, type);
			var.setParamIndex(v.getParamIndex());
		} else if (scope instanceof ClassScope) {
			var = new Variable(ScopeType.CLASS_SCOPE, name, type);
		} else if (scope instanceof LocalScope) {
			var = new Variable(ScopeType.LOCAL_SCOPE, name, type);
		}
		var.setScopeName(scope.getName());
		v.setVariable(var);
	}

	public Object visit(ASTSelectionStatement node, Object data) {
		createLocalScope(node);
		cont(node, data);
		return data;
	}

	public Object visit(ASTDeclarationSpecifiers node, Object data) {
		if (!node.isTypehandled()) {
			for (ASTDeclarationSpecifiers d : node
					.findAllNestDeclarationSpecifiers()) {
				d.setTypehandled(true);
			}
			node.setTypehandled(false);
		}
		super.visit(node, data);

		if (!node.isTypehandled()) {
			CType type = null;
			node.setTypehandled(true);
			List<ASTTypeSpecifier> typelist = node.findAllNestTypeSpecifier();
			if (typelist.size() > 0) {
				if (typelist.get(0).getType() instanceof CType_BaseType
						|| typelist.get(0).getImage().equalsIgnoreCase(
								"unsigned")) {
					StringBuffer buff = new StringBuffer();
					for (ASTTypeSpecifier t : typelist) {
						if (t.getImage().equalsIgnoreCase("unsigned")) {
							buff.append(t.getImage() + " ");
						} else if (t.getType() != null) {
							buff.append(t.getType().getName() + " ");
						}
					}
					type = CType_BaseType.getBaseType(buff.toString().trim());
				} else if (typelist.get(0).getType() instanceof CType_BaseType
						|| typelist.get(0).getImage()
								.equalsIgnoreCase("signed")) {
					StringBuffer buff = new StringBuffer();
					for (ASTTypeSpecifier t : typelist) {
						if (t.getImage().equalsIgnoreCase("signed")) {
							buff.append(t.getImage() + " ");
						} else {
							buff.append(t.getType().getName() + " ");
						}
					}
					type = CType_BaseType.getBaseType(buff.toString().trim());
				} else {
					type = typelist.get(0).getType();
				}
			} else {
				type = CType_BaseType.getBaseType("int");
			}

			List<ASTTypeQualifier> qualist = node.findAllNestTypeQualifier();
			if (qualist.size() > 0 && type != null) {
				CType_Qualified qtype = new CType_Qualified(type);
				for (ASTTypeQualifier q : qualist) {
					qtype.addQualifier(q.getImage());
					type = qtype;
				}
			}
			node.setType(type);
		}

		return data;
	}

	public Object visit(ASTSpecifierQualifierList node, Object data) {
		if (!node.isTypehandled()) {
			for (ASTSpecifierQualifierList d : node
					.findAllNestSpecifierQualifierList()) {
				d.setTypehandled(true);
			}
			node.setTypehandled(false);
		}
		super.visit(node, data);

		if (!node.isTypehandled()) {
			node.setTypehandled(true);
			List<ASTTypeSpecifier> typelist = node.findAllNestTypeSpecifier();
			if (typelist.size() == 1 && (typelist.get(0).getImage().equals("unsigned") || 
										 typelist.get(0).getImage().equals("signed"))) {
				node.setType(CType_BaseType.getBaseType("int"));
			}else if (typelist.size() > 0) {				
				int i=0;
				//zys:2010.4.15	跳过类型信息起始处的unsigned
				while(i<typelist.size() && (typelist.get(i).getImage().equals("unsigned") ||
											typelist.get(i).getImage().equals("signed"))){
					i++;
				}
				if (typelist.get(i).getType() instanceof CType_BaseType) {
					StringBuffer buff = new StringBuffer();
					for (ASTTypeSpecifier t : typelist) {
						if(t.getImage().equals("unsigned") || t.getImage().equals("signed"))
							buff.append(t.getImage()+" ");
						else
							buff.append(t.getType().getName() + " ");
					}
					node.setType(CType_BaseType.getBaseType(buff.toString()
							.trim()));
				} else {
					node.setType(typelist.get(i).getType());
				}
			}

			List<ASTTypeQualifier> qualist = node.findAllNestTypeQualifier();
			CType type = node.getType();
			if (qualist.size() > 0 && type != null) {
				CType_Qualified qtype = new CType_Qualified(type);
				for (ASTTypeQualifier q : qualist) {
					qtype.addQualifier(q.getImage());
				}
				node.setType(qtype);
			}
		}
		return data;
	}

	public Object visit(ASTTypeSpecifier node, Object data) {
		super.visit(node, data);
		String image = node.getImage();
		if (image.equals("")) {
			Node firstchild = node.jjtGetChild(0);
			if (firstchild instanceof ASTStructOrUnionSpecifier) {
				node
						.setType(((ASTStructOrUnionSpecifier) firstchild)
								.getType());
			} else if (firstchild instanceof ASTEnumSpecifier) {
				node.setType(((ASTEnumSpecifier) firstchild).getType());
			} else if (firstchild instanceof ASTTypedefName) {
				node.setType(((ASTTypedefName) firstchild).getType());
			} else {
				node.setType(((ASTTypeofDeclarationSpecifier) firstchild)
						.getType());
			}
		} else {
			// zys:如果当前限定符为unsigned或signed,则暂时不生成类型信息，而是在上层节点合并后生成类型信息
			if (!image.equalsIgnoreCase("unsigned")
					&& !image.equalsIgnoreCase("signed"))
				node.setType(CType_BaseType.getBaseType(image));
		}
		return data;
	}

	public Object visit(ASTTypedefName node, Object data) {
		Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
		String image = node.getImage();
		node.setType(s.getType(image));
		return data;
	}

	public Object visit(ASTInitDeclarator node, Object data) {
		super.visit(node, data);
		ASTDeclarator de = (ASTDeclarator) node
				.getFirstDirectChildOfType(ASTDeclarator.class);
		if (de == null) {
			throw new RuntimeException(
					"AST tree error,InitDeclarator use error!");
		}

		node.setType(de.getType());
		return data;
	}

	public Object visit(ASTStructDeclarator node, Object data) {
		super.visit(node, data);
		ASTDeclarator de = (ASTDeclarator) node
				.getFirstDirectChildOfType(ASTDeclarator.class);
		// zys: struct s{int i:4;char c:4;};
		if (node.jjtGetNumChildren() == 2) {
			ASTConstantExpression ce = (ASTConstantExpression) node
					.jjtGetChild(1);
			int bitfield = ce.getIntegerValue();

			CType originaltype = de.getType();
			CType_BitField type = new CType_BitField();
			type.setOriginaltype(originaltype);
			type.setBitfield(bitfield);

			node.setType(type);
			return data;
		} else if (de != null) {
			node.setType(de.getType());
		} else if (node.jjtGetNumChildren() == 1) {// 针对没有变量的声明情况
			if (node.jjtGetChild(0) instanceof ASTConstantExpression)
				return data;
		} else {
			throw new RuntimeException(
					"ASTStructDeclarator should always have a ASTDeclarator!");
		}
		return data;
	}

	public Object visit(ASTStructDeclaration node, Object data) {
		//zys:2010.10.21	struct s{int i; ;};
		if(node.jjtGetNumChildren()==0)
			return data;
		ASTSpecifierQualifierList ds = (ASTSpecifierQualifierList) node
				.jjtGetChild(0);
		ds.jjtAccept(this, data);
		typecontex.push(ds.getType());
		for (int i = 1; i < node.jjtGetNumChildren(); ++i) {
			node.jjtGetChild(i).jjtAccept(this, data);
		}

		ASTStructDeclaratorList dl = (ASTStructDeclaratorList) node
				.getFirstDirectChildOfType(ASTStructDeclaratorList.class);

		if (dl != null) {
			CType type = typecontex.peek();
			for (int i = 0; i < dl.jjtGetNumChildren(); i++) {
				ASTStructDeclarator sd = (ASTStructDeclarator) dl
						.jjtGetChild(i);
				CType dtype = sd.getType();
				if (dtype != null) {
					CType.setOrignType(dtype, type);
					type = dtype;
				}
				sd.setType(type);

				ASTDeclarator de = (ASTDeclarator) sd
						.getFirstDirectChildOfType(ASTDeclarator.class);
				if (de != null) {
					de.setType(type);
					ASTDirectDeclarator temp = de.getFinalDirectDeclarator();
					temp.setType(type);
					temp.getDecl().setType(type);
					//add by zhouhb
					//2011.4.27
					if(Config.Field){
						ASTStructOrUnionSpecifier str=(ASTStructOrUnionSpecifier)node.getFirstParentOfType(ASTStructOrUnionSpecifier.class);
						if(str.getType() instanceof CType_Struct){
							((CType_Struct)str.getType()).addType(de.getImage(), type);
						}
					}
					//end by zhouhb
				}
			}
		}
		typecontex.pop();
		return data;
	}

	public Object visit(ASTDeclaration node, Object data) {
		ASTDeclarationSpecifiers ds = (ASTDeclarationSpecifiers) node
				.jjtGetChild(0);
		boolean isstatic = false, isExtern = false;
		ASTStorageClassSpecifier storage = (ASTStorageClassSpecifier) node.getFirstChildOfType(ASTStorageClassSpecifier.class) ;
		while( storage != null) {
			if (storage.getImage().equals("static")) {
				isstatic = true;
			}
			else if (storage.getImage().equals("extern")) {
				isExtern = true;
			}
			if(((ASTDeclarationSpecifiers)storage.jjtGetParent()).getFirstChildOfType(ASTDeclarationSpecifiers.class) == null)
				break;
			else if(((ASTDeclarationSpecifiers)storage.jjtGetParent()).getFirstChildOfType(ASTDeclarationSpecifiers.class).jjtGetChild(0) instanceof ASTStorageClassSpecifier)
				storage = (ASTStorageClassSpecifier) ((ASTDeclarationSpecifiers)storage.jjtGetParent()).getFirstChildOfType(ASTDeclarationSpecifiers.class).jjtGetChild(0);
			else 
				break; 
				
		}
		ds.jjtAccept(this, data);
		typecontex.push(ds.getType());
		for (int i = 1; i < node.jjtGetNumChildren(); ++i) {
			node.jjtGetChild(i).jjtAccept(this, data);
		}
		
		Scope s = ((SimpleNode) node.jjtGetParent()).getScope();
		ASTInitDeclaratorList dl = (ASTInitDeclaratorList) node
				.getFirstDirectChildOfType(ASTInitDeclaratorList.class);
		if (dl != null) {
			for (int i = 0; i < dl.jjtGetNumChildren(); i++) {
				CType type = typecontex.peek();
				ASTInitDeclarator init = (ASTInitDeclarator) dl.jjtGetChild(i);

				ASTDeclarator de  = null;
				if (CParser.getType().equalsIgnoreCase("keil")){
					if(init.jjtGetChild(0)instanceof ASTConstant && init.jjtGetChild(1)instanceof ASTDeclarator ){
						de = (ASTDeclarator) init.jjtGetChild(1);
					}else{
						de = (ASTDeclarator) init.jjtGetChild(0);
					}
				}else{
					 de = (ASTDeclarator) init.jjtGetChild(0);
				}
			
				CType dtype = de.getType();
				if (dtype == null) {
					de.setType(type);
				}
				CType.setOrignType(dtype, type);

				if (dtype != null) {
					type = dtype.getSimpleType();
				}
				if (type instanceof CType_Array) {
					CType_Array atype = (CType_Array) type;
					if (init.jjtGetNumChildren() > 1
							&& init.jjtGetChild(1) instanceof ASTInitializer && !atype.isFixed()) {
						// 处理缺省的数组维数
						ASTInitializer initializer = (ASTInitializer) init
								.jjtGetChild(1);
						List<Integer> dims = initializer.getDimSize();
						for (int dim : dims) {
							if (atype.getDimSize() < dim) {
								atype.setDimSize(dim);
							}
							type = atype.getOriginaltype().getSimpleType();
							if (type instanceof CType_Array) {
								atype = (CType_Array) type;
							} else {
								break;
							}
						}
					}
				}

				// 处理所有的typedef
				ASTDirectDeclarator d = de.getFinalDirectDeclarator();
				if (d.getDecl() instanceof ClassNameDeclaration) {
					ClassNameDeclaration decl = (ClassNameDeclaration) d
							.getDecl();
					CType_Typedef ttype = new CType_Typedef(d.getImage());
					ttype.setOriginaltype(d.getTopDeclarator().getType());
					s.addType(ttype.getName(), ttype);
					decl.setType(ttype);
				} else if (d.getDecl() instanceof VariableNameDeclaration) {
					VariableNameDeclaration decl = (VariableNameDeclaration) d
							.getDecl();
					if(isstatic)
						decl.setStatic(true);
					if(isExtern)
						decl.setExtern(true);
					decl.setType(d.getTopDeclarator().getType());
					//add by zhouhb
					//2011.5.4
					//当声明复杂数据结构实例后，对其内部成员变量逐一进行声明
					if(Config.Field){
						if(decl.getType()instanceof CType_Struct||(decl.getType()instanceof CType_Pointer&&(((CType_Pointer)decl.getType()).getDeepOriginaltype()instanceof CType_Struct))){
							structMemDeclaration(de.getImage(),type,s,node.getFileName(),de,0);
							if(d.getVariableNameDeclaration()!=null){
								d.getVariableNameDeclaration().mems=de.decl;
							}
						}else if(decl.getType() instanceof CType_Typedef && ((CType_Typedef)decl.getType()).getOriginaltype() instanceof CType_Struct){
							structMemDeclaration(de.getImage(),((CType_Typedef)decl.getType()).getOriginaltype(),s,node.getFileName(),de,0);
							if(d.getVariableNameDeclaration()!=null){
								d.getVariableNameDeclaration().mems=de.decl;
							}
						}
						else if(decl.getType()instanceof CType_Pointer){
							pointersDeclaration((CType_Pointer)decl.getType(),node.getScope(),node.getFileName(),de,de.getImage(),0);
						}else if(decl.getType() instanceof CType_Array && ((CType_Array)decl.getType()).getMemNum()<=Config.MaxArray){
							arrayMemDeclaration(d.getImage(),(CType_Array)decl.getType(),node.getScope(),node.getFileName(),de,0);
						}						
					}
				}

				// zys:2010.3.21 如果变量声明时同时进行了初始化赋值，则取得该初始值
				// liuli:2010.3.24 temp取值有可能为空
				if (de.getNextSibling() instanceof ASTInitializer) {
					Node temp = ((SimpleNode) (de.getNextSibling()))
							.getFirstChildOfType(ASTConstant.class);
					if (temp == null) {
						continue;
					}
					ASTConstant constant = (ASTConstant) temp;
					VariableNameDeclaration v = de.getVariableNameDeclaration();
					if (v != null) {
						setInitializedVariable(v);
						if (v.getType() instanceof CType_Array
								|| v.getType() instanceof CType_Pointer) {
							// 如果是数组或指针类型的初始化
							v.getVariable().setValue(PointerValue.NOTNULL);
						} else if (v.getType() instanceof CType_BaseType) {
							v.getVariable().setValue(
									computeIntegerConstant(constant));
						} else if (v.getType() instanceof CType_Struct) {
							v.getVariable().setValue(
									PointerValue.NULL_OR_NOTNULL);

						}
					}
				}//增加了全局变量未初始化时的默认值设置
				 //修改后可能造成一些函数间缺陷
				 //add by zhouhb 2010/8/6
//				else if(s instanceof SourceFileScope){
//					VariableNameDeclaration v = de.getVariableNameDeclaration();
//					if (v != null) {
//						setInitializedVariable(v);
//						if (type==CType_BaseType.doubleType||type==CType_BaseType.floatType||type==CType_BaseType.intType||type==CType_BaseType.longDoubleType||
//								type==CType_BaseType.longLongType||type==CType_BaseType.longType||type==CType_BaseType.shortType||type==CType_BaseType.uIntType||
//								type==CType_BaseType.uLongLongType||type==CType_BaseType.uLongType||type==CType_BaseType.uShortType) {
//							v.getVariable().setValue((long)0);
//						}
//					}
//				}
			}
		} else {
			// liuli:在函数中typedef自定义的类型名称有可能与全局中typedef定义的一样，需要正确检测该类型
			List<Node> list = node.findChildrenOfType(ASTTypedefName.class);
			List<Node> listTs = node.findChildrenOfType(ASTTypeSpecifier.class);
			if (list.size() != 0 && listTs.size() != 0) {
				ASTTypedefName tn = (ASTTypedefName) list.get(0);
				ASTTypeSpecifier ts = (ASTTypeSpecifier) tn.jjtGetParent();
				if (tn != null && ts != null) {
					if(ts.jjtGetParent() instanceof ASTDeclarationSpecifiers){
						ASTDeclarationSpecifiers n = (ASTDeclarationSpecifiers)node.getFirstChildOfType(ASTDeclarationSpecifiers.class);
						if(n!= null){
							CType_Typedef ttype = new CType_Typedef(tn.getImage());
							ttype.setOriginaltype(n.getType());
							s.addType(ttype.getName(), ttype);
						}
					}
					
				}
			}
		}
		typecontex.pop();
		/*zys:2011.3.14	
		 * GCC与KEIL都允许这种类型的函数定义：void f(i,j)int i;int j;{},此时ASTDeclarationList中
		 * 的变量声明应该处理为参数声明；
		 * 但KEIL的语法在void f(){int f;}这种情况下，ASTDeclarationList下即为ASTDeclaration，
		 * 这种情况不应该处理为参数声明*/
		if(node.jjtGetParent() instanceof ASTDeclarationList
				&& node.jjtGetParent().jjtGetParent() instanceof ASTFunctionDefinition){
			SimpleNode parent = (SimpleNode) node.getFirstChildOfType(ASTInitDeclaratorList.class);
			for (int k = 0; k < parent.jjtGetNumChildren(); k++) {
				ASTInitDeclarator initDitectDec = (ASTInitDeclarator) parent.jjtGetChild(k);
				ASTDirectDeclarator directDec = (ASTDirectDeclarator) (initDitectDec
						.getFirstChildOfType(ASTDirectDeclarator.class));
				if (directDec == null)
					continue;
				if (directDec.getVariableNameDeclaration() != null){
					directDec.getVariableNameDeclaration().setParamIndex(paramIndex);
					paramIndex++;
				}
			}
		}
		return data;
	}

	public Object visit(ASTTypeofDeclarationSpecifier node, Object data) {
		super.visit(node, data);
		Node firstchild = node.jjtGetChild(0);
		if (firstchild instanceof ASTTypeName) {
			node.setType(((ASTTypeName) firstchild).getType());
		} else if (firstchild instanceof ASTAssignmentExpression) {
			firstchild.jjtAccept(new OccurrenceAndExpressionTypeFinder(), null);
			node.setType(((ASTAssignmentExpression) firstchild).getType());
		}

		return data;
	}

	private void cont(SimpleNode node, Object data) {
		super.visit(node, data);
		scopes.pop();
	}

	public Object visit(ASTConstant node, Object data) {
		Object o = computeIntegerConstant(node);
		if (o.getClass() == Long.class) {
			long value = ((Long) computeIntegerConstant(node)).longValue();
			node.setValue(value);
		}
		return data;
	}

	/**
	 * 计算常量结点的真实值（主要针对数值型）
	 * 
	 * @param node
	 * @return
	 */
	private Object computeIntegerConstant(ASTConstant node) {
		String image = node.getImage();
		if (image.startsWith("\"")) {
			return node.getImage();
		} else if (image.startsWith("\'")) {
			return node.getImage();
		} else {
			if (image.endsWith("l") || image.endsWith("L")
					|| image.endsWith("u") || image.endsWith("U")) {
				image = image.substring(0, image.length() - 1);
			}
			char[] source = image.toCharArray();
			int length = source.length;
			long intValue = 0;
			long computeValue = 0L;
			try {
				if (source[0] == '0') {
					if (length == 1) {
						computeValue = 0;
					} else {
						final int shift, radix;
						int j;
						if ((source[1] == 'x') || (source[1] == 'X')) {
							shift = 4;
							j = 2;
							radix = 16;
						} else {
							shift = 3;
							j = 1;
							radix = 8;
						}
						while (source[j] == '0') {
							j++; // jump over redondant zero
							if (j == length) { // watch for 000000000000000000
								computeValue = 0;
								break;
							}
						}
						while (j < length) {
							int digitValue = 0;
							if (radix == 8) {
								if ('0' <= source[j] && source[j] <= '7') {
									digitValue = source[j++] - '0';
								} else {
									throw new RuntimeException(
											"This is not a legal integer");
								}
							} else {
								if ('0' <= source[j] && source[j] <= '9') {
									digitValue = source[j++] - '0';
								} else if ('a' <= source[j] && source[j] <= 'f') {
									digitValue = source[j++] - 'a' + 10;
								} else if ('A' <= source[j] && source[j] <= 'F') {
									digitValue = source[j++] - 'A' + 10;
								} else if (source[j] == 'u' || source[j] == 'l'
										|| source[j] == 'U' || source[j] == 'L') {
									j++;
									continue;
								} else {
									throw new RuntimeException(
											"This is not a legal integer");
								}
							}
							computeValue = (computeValue << shift) | digitValue;

						}
					}
				} else { // -----------regular case : radix = 10-----------
					for (int i = 0; i < length; i++) {
						int digitValue;
						if ('0' <= source[i] && source[i] <= '9') {
							digitValue = source[i] - '0';
						} else if (source[i] == 'u' || source[i] == 'l'
								|| source[i] == 'U' || source[i] == 'L') {
							continue;
						} else {
							throw new RuntimeException(
									"This is not a legal integer");
						}
						computeValue = 10 * computeValue + digitValue;
					}
				}
				intValue = computeValue;

			} catch (RuntimeException e) {
			}

			return intValue;
		}
	}
	
	//将成员变量仅对下一层进行关联，如a只记录a.b，不记录a.b.c
	//add by zhouhb
	private void addToParent(VariableNameDeclaration child, String parent){
		NameDeclaration parentDecl = Search.searchInVariableUpward(parent, child.getScope());
		try{
			if (parentDecl instanceof VariableNameDeclaration){
				((VariableNameDeclaration)parentDecl).mems.add(child);
			}else{
				throw new RuntimeException(
				"Cannot find variable"+parent);
			}
		}catch (RuntimeException e) {
		}
	}
}
