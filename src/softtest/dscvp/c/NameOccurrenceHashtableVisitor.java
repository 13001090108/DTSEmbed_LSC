package softtest.dscvp.c;

import java.util.Hashtable;

import softtest.cfg.c.Edge;
import softtest.cfg.c.Graph;
import softtest.cfg.c.GraphVisitor;
import softtest.cfg.c.VexNode;
import softtest.symboltable.c.NameOccurrence;

public class NameOccurrenceHashtableVisitor implements GraphVisitor{

	public void visit(VexNode n, Object data) {
		// TODO Auto-generated method stub
		if (n.getOccurrences() == null || n.getOccurrences().size() == 0)
			return;
		Hashtable<String, NameOccurrence> occtable = n.getGraph().getOcctable();
		for (NameOccurrence occ:n.getOccurrences()){
			if (occtable.containsKey(occ.toString())){
				if (occ.getOccurrenceType() == NameOccurrence.OccurrenceType.DEF){
					occtable.put(occ.toString(), occ);
				}
			}else{
				occtable.put(occ.toString(), occ);
			}
		}
	}
	
	public void visit(Edge e, Object data) {
		// TODO Auto-generated method stub
		
	}
	
	public void visit(Graph g, Object data) {
		// TODO Auto-generated method stub
		
	}
}
