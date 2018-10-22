import java.util.Hashtable;                                          
    public class test {                                                  
    	public void process() {                                             
    		Hashtable numbers = new Hashtable();                               
    		numbers.put("one", new Integer(1));                                
    		Integer n = (Integer)numbers.get("two");                           
    		return;                                                            
    	}                                                                   
}
