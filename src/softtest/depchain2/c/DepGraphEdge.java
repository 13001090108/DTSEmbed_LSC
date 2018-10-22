package softtest.depchain2.c;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import softtest.cfg.c.VexNode;

public class DepGraphEdge {
	//public List<VexNode> paths = new ArrayList<>(); Ó°ÏìÂ·¾¶ÔÙ¿¼ÂÇ
	public int depType;
	
	public Map<String, Boolean> predicateMap = new HashMap<>();
	
	public DepGraphNode head,tail;
	
}
