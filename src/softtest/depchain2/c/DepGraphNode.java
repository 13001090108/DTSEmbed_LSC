package softtest.depchain2.c;

import java.util.ArrayList;
import java.util.List;

import softtest.scvp.c.Position;

public class DepGraphNode {
	public Position p;
	public String occ;
	public List<DepGraphEdge> inedges = new ArrayList<>();
	public List<DepGraphEdge> outedges = new ArrayList<>();
	
	public void addSubNode(Position p,String occ) {
		DepGraphEdge edge = new DepGraphEdge();
		DepGraphNode newNode = new DepGraphNode();
		
		newNode.p = p;
		newNode.occ = occ;
		
		outedges.add(edge);
		newNode.inedges.add(edge);
		
		edge.head = this;
		edge.tail = newNode;
	}
}
