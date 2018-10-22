/**
 * 
 */
package softtest.cluster.c;

/**
 * @author：JJL
 * @date: 2016年10月10日
 * @description:
 */
import java.util.HashSet;
import java.util.List;

import softtest.dscvp.c.DSCVPElement;
/** 
 * @auto:JJL,2016.8.10
 * TODO : 封装数据库
 */  
public class SimpleBean {
	private String Num;  
    private String Fault; 
    private String Category; 
    private String Variable;
    private String File;
    private String Method;
//    private String Module;
    private String StartLine;//int
    private String IPLine;//int
//    private String IPLineCode;
//    private String Judge;
//    private String Review;//bool
//    private String Description;
//    private String PreConditions;
//    private String TraceInfo;
//    private String Code;
//    private String Feature;
//    private String DExpansion;
    private String stringF;
    private DSCVPElement F;
    private String Equal; 
    private String Related; 
    private boolean similarVisited = false;
    private boolean similarInclusion = false;
    private HashSet<String> SimilarInclusionAlarm = new HashSet<String>();
    
    public SimpleBean(String Num, String Fault, String Category, String Variable,String stringF, DSCVPElement F, 
    		String Equal, String Related, String File, String Method, String StartLine, String IPLine) {
    	this.Num = Num;
    	this.Fault = Fault;
    	this.Category = Category;
    	this.Variable = Variable;
    	this.stringF = stringF;
    	this.F = F;
    	this.Equal = Equal;
    	this.Related = Related;
    	
    	this.File = File;
    	this.Method = Method;
    	this.StartLine = StartLine;
    	this.IPLine = IPLine;
    			
    }
    
    /** 相似关系确认*/
    public void visitSimilar(boolean visit) {
    	this.similarVisited = visit;
    }
    public boolean getVisited() {
    	return this.similarVisited;
    }
    
    /** 相似关系蕴含点*/
    public void setSimilarInclusion (boolean similarInclusion) {
    	this.similarInclusion = similarInclusion;
    }
    public boolean getSimilarInclusion () {
    	return this.similarInclusion;
    }
    
    /** Num*/
    public void setNum(String Num){  
        this.Num = Num;  
    }  
    public String getNum(){  
        return this.Num;
    }  
    /** Fault*/
    public void setFault(String Fault){  
        this.Fault = Fault;  
    }  
    public String getFault(){  
        return this.Fault;
    }
    /** Category*/
    public void setCategory(String Category){  
        this.Category = Category;  
    }  
    public String getCategory(){  
        return this.Category;
    }
    /** File*/
    public void setFile(String File){  
        this.File = File;  
    }  
    public String getFile(){  
        return this.File;
    }
    /** Method*/
    public void setMethod(String Method){  
        this.Method = Method;  
    }  
    public String getMethod(){  
        return this.Method;
    }
    /** StartLine*/
    public void setStartLine(String StartLine){  
        this.StartLine = StartLine;  
    }  
    public String getStartLine(){  
        return this.StartLine;
    }
    /** StringF*/
    public void setStringF(String StringF){  
        this.stringF = StringF;  
    }  
    public String getStringF(){  
        return this.stringF;
    }
    /** Variable*/
    public void setVariable(String Variable){  
        this.Variable = Variable;  
    }  
    public String getVariable(){  
        return this.Variable;
    }
    /** F feature */
    public void setF(DSCVPElement F) {
    	this.F = F;
    }
    public DSCVPElement getF() {
    	return this.F;
    }
    /** Equal*/
    public void setEqual(String Equal){  
        this.Equal = Equal;  
    }  
    public String getEqual(){  
        return this.Equal;
    }
    /** Related*/
    public void setRelated(String Related){  
        this.Related = Related;  
    }  
    public String getRelated(){  
        return this.Related;
    }

	/**SimilarInclusionAlarm */
	public void setSimilarInclusionAlarm(String number) {
		this.SimilarInclusionAlarm.add(number);
	}
	public HashSet getSimilarInclusionAlarm() {
		return this.SimilarInclusionAlarm;
	}
}

