package softtest.cfg.c;

import java.io.*;
import java.util.*;

import softtest.config.c.*;

/** 用于产生.dot文件的控制流图访问者 */
public class DumpGraphVisitor implements GraphVisitor { // 对图遍历的访问者接口
	/** 访问控制流图的节点，打印节点名字，当前的变量域集，条件限定域集 */
	public void visit(VexNode n, Object data) {
		FileWriter out = (FileWriter) data;
		try {
			String s = "";
			
			if(Config.DUMP_SYMBOL){
				s=s+n.getValueSet();
			}
			if(Config.DUMP_DOMAIN){
				s = s + "\\n"+n.getVarDomainSet();
				//n.getStructDomain("test");
				if (n.getCondata() != null) {
					s = s + "\\n" + n.getCondata();
				}
			}
			
			s = s+"\"" ;
			if (n.getContradict()) {
				s = s + ",color=red";
			}
			out.write(n.name + "[label=\"" + n.name + "\\n" + s + "];\n");
		} catch (IOException ex) {
		}
	}

	/** 访问控制流图的边，打印名字 */
	public void visit(Edge e, Object data) {
		FileWriter out = (FileWriter) data;
		try {
			String s = null;
			s = e.tailnode.name + " -> " + e.headnode.name + "[label=\"" + e.name + "\"";
			if (e.getContradict()) {
				s = s + ",color=red";
			}
			s = s + "];\n";
			out.write(s);
		} catch (IOException ex) {
		}
	}

	/** 访问控制流图，遍历访问其节点集合和边集合 */
	public void visit(Graph g, Object data) {
		FileWriter out = null;
		try {
			out = new FileWriter((String) data);
			out.write("digraph G {\n");

			for (Enumeration<VexNode> e = g.nodes.elements(); e.hasMoreElements();) {
				VexNode n = e.nextElement();
				visit(n, out);
			}

			for (Enumeration<Edge> e = g.edges.elements(); e.hasMoreElements();) {
				Edge edge = e.nextElement();
				visit(edge, out);
			}
			out.write(" }");
			
		} catch (IOException ex) {
		}
		//modified by liuyan 2015.6.3
		finally{
			if( out != null ){
				try {
					out.close();
				} catch (IOException e) {
					// TODO Auto-generated catch block
					e.printStackTrace();
				}
			}
		}
	}
}
