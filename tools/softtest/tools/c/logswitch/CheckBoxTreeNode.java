package softtest.tools.c.logswitch;  
 
import javax.swing.tree.DefaultMutableTreeNode;  
 
public class CheckBoxTreeNode extends DefaultMutableTreeNode  
{  
    protected boolean isSelected;  
      
    public CheckBoxTreeNode()  
    {  
        this(null);  
    }  
      
    public CheckBoxTreeNode(Object userObject)  
    {  
        this(userObject, true, false);  
    }  
      
    public CheckBoxTreeNode(Object userObject, boolean allowsChildren, boolean isSelected)  
    {  
        super(userObject, allowsChildren);  
        this.isSelected = isSelected;  
    }  
 
    public boolean isSelected()  
    {  
        return isSelected;  
    }  
      
    public void setSelected(boolean _isSelected)  
    {  
        this.isSelected = _isSelected;  
          
        if(_isSelected)  
        {  
        	CheckBoxTreeNode pNode = (CheckBoxTreeNode)parent;  
            if(pNode != null && pNode.isSelected() != _isSelected){  
            	this.isSelected = false ;
            	return ;
            }
            if(children != null)  
            {  
                for(Object obj : children)  
                {  
                    CheckBoxTreeNode node = (CheckBoxTreeNode)obj;  
                    if(_isSelected != node.isSelected())  
                        node.setSelected(_isSelected);  
                }  
            }   
        }  
        else   
        {  
            if(children != null)  
            {  
            	for(int i = 0; i < children.size(); ++ i)  
            	{  
            		CheckBoxTreeNode node = (CheckBoxTreeNode)children.get(i);  
                    if(node.isSelected() != _isSelected)  
                    	node.setSelected(_isSelected);  
                }  
            }  
        }  
    }  
} 