package softtest.domain.c.analysis;

import java.util.ArrayList;
import java.util.List;

import softtest.cfg.c.VexNode;
import softtest.domain.c.symbolic.Expression;

public class ExpressionVistorData {
    public Expression value;
    
    /** 控制是否产生副作用的标志 */
    public boolean sideeffect=true;
    
    public VexNode currentvex=null;
       
    public List<Integer> arrayIndex=new ArrayList<Integer>();   
}
