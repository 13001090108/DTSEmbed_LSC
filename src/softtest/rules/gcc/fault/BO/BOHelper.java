package softtest.rules.gcc.fault.BO;



import java.util.ArrayList;
import java.util.List;
import softtest.ast.c.ASTConstant;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.SimpleNode;

import softtest.rules.c.StateMachineUtils;
import softtest.rules.gcc.fault.BOStateMachine;

/**
 * Calculate the exact length of for the format strings.
 * 
 * modified by chh
 */
public class BOHelper {
	
	private SimpleNode curFuncNode;
	private String curFormatStr;
	private BOFunction boFunc;
	
	/*true：对于bo函数 func(source,format,src)中的src本身为  函数参数或者函数，认为src它的大小为无限大，
    		会发生溢出；可能带来误报
     false: 不做处理，可能带来漏报 */
	public static boolean unknownTypeAsMax = true;

	public BOHelper(String formatStr, SimpleNode funcNode, BOFunction func) {
		this.curFormatStr = formatStr;
		this.curFuncNode = funcNode;
		this.boFunc = func;
	}
	

	/**
	 * Get the mapping unsigned value to the hex string.
	 * @param hexInteger
	 * @return
	 */
	private long getUnsignedValue(String hexInteger) {
		long value = 0; //value must be long. because when hexInteger equals "ffffffff" ;int value would be -1 again.
		int len = hexInteger.length();
		hexInteger = hexInteger.toLowerCase();
		
		for (int i = 0; i < len; ++i) {
			char c = hexInteger.charAt(i);
			value *= 16;
			
			switch (c) {
			
			case 'a':
				value += 10;
				break;
			case 'b':
				value += 11;
				break;
			case 'c':
				value += 12;
				break;
			case 'd':
				value += 13;
				break;
			case 'e':
				value += 14;
				break;
			case 'f':
				value += 15;
				break;
			default:
				value += (c-'0');
				break;
			}
		}
		
		return value;
	}
	
	/**
	 * Get the length of a constant string, a array or a pointor to a array.
	 * @param argIndex
	 * @return
	 */
	private long getStringLength(int argIndex) {
		long len = 0;
		
		SimpleNode argNode = StateMachineUtils.getArgument(curFuncNode, boFunc.srcIndex+argIndex);
		if (argNode == null) {
			return -1;
		}
			
		//1. check whether the argument is a constant string or not.
		SimpleNode priNode = (SimpleNode) argNode.getSingleChildofType(ASTPrimaryExpression.class);
		if (priNode!=null&& priNode.getSingleChildofType(ASTConstant.class)!=null&&!((ASTPrimaryExpression)priNode).isMethod()) { //constant string
			SimpleNode constantNode = (SimpleNode) priNode.getSingleChildofType(ASTConstant.class);
			String string = constantNode.getImage();
			
			if (string.startsWith("\"")) {
				string = string.substring(1);
			} else if (string.startsWith("L\"")) {
				string = string.substring(2);
			}
			
			if (string.endsWith("\"")) {
				string = string.substring(0, string.length()-1);
			}
			
			len = getConstStringLength(string);
		} else if(priNode!=null&&priNode.jjtGetNumChildren()==0){
			ASTPrimaryExpression argPreNode=(ASTPrimaryExpression) argNode.getFirstChildInstanceofType(ASTPrimaryExpression.class);
			len=BOStateMachine.getsrclength(argPreNode);
			if(len!=0)
			--len; //sub the '\0'
		}
		
		return len;
	}
	
	/**
	 * Get the length for a constant string.
	 * @param string
	 * @return
	 */
	private static int getConstStringLength(String string) {
		int strLen = string.length();
		int totalLen = 0;
		int i = 0;
		
		while (i < strLen) {
			char c = string.charAt(i);
			if (c == '\\') {
				++totalLen;
				i += 2;
			} else {
				++totalLen;
				++i;
			}
		}
		
		return totalLen; 
	}
	
	/**
	 * Visit the format string to calculate the length of the format string. 
	 * Such as the "%d%s%u%x" in sprintf(buf, "%d%s%u%x", arg0, arg1, arg2, arg3)
	 * @return
	 */
	public long getForStrLength() {
		long totalLen = 0;
		int m = 0, n = 0;//%m.nf %md %ms etc...
		boolean isStart = false;
		boolean hasDot = false;
		int strLen = curFormatStr.length();
		int argIndex = 0; //specify the ith argument.
		
		//start to visit the format string using FSM.
		for (int curPos = 0; curPos < strLen;) {
			char curChar = curFormatStr.charAt(curPos);

			if (!isStart) { //not start another valid format string.
				if (curChar == '%') { //check the next char.
					if (curPos+1 < strLen) {
						char nextChar = curFormatStr.charAt(curPos+1);
						if (nextChar == '%') { //then not started yet.
							curPos += 2;
							++totalLen;
						} else if (nextChar == '-') { //such as %-d
							curPos += 2;
							isStart = true;
							++argIndex;
						} else {
							++curPos;
							isStart = true;
							++argIndex;
						}
					}
				} else if (curChar == '\\'){
					curPos += 2;
					++totalLen;
				} else if (curChar >= 255){  //unicode：Chinese
					++curPos;
					totalLen += 2;
				} else { //ASIIC: letters, numbers or other symbols.
					++curPos;
					++totalLen;
				}
			} else { //started.
				/**
				 * Calculate m.
				 */
				if (curChar >= '0' && curChar <= '9') { //start to calculate m.
					m = curChar-'0';
					++curPos;
					
					for (; curPos < strLen; ++curPos) {
						curChar = curFormatStr.charAt(curPos);
						if (curChar < '0' || curChar > '9') {
							break;
						}
						
						m = m*10 + (curChar-'0');
					}
				}//finished calculating m.
				
				/**
				 * Calculate n.
				 */
				if (curChar == '.') { //such as %.nd or %m.nf then start to calculate n.
					++curPos;
					hasDot = true;
					
					for (; curPos < strLen; ++curPos) {
						curChar = curFormatStr.charAt(curPos);
						if (curChar < '0' || curChar > '9') {
							break;
						}
						
						n = n*10 + (curChar-'0');
					}
				} //finished calculating n.
				
				/**
				 * Calculate the exact length of the arguments.
				 */
				long len = 0;
				long value = 0;//getIntegerValue(argIndex);
				boolean hasCal = false;
				
				for (; curPos < strLen; ++curPos) {
					curChar = curFormatStr.charAt(curPos);
					switch (curChar) {
					case 'd':case 'i':
						m = m > n ? m : n;
						hasCal = true;
						value = argIndex;
						len = Long.toString(value).length();
						len = len >= m ? len : m;
						break;
					case 'u':
						m = m > n ? m : n;
						hasCal = true;
						value = argIndex;
						value = getUnsignedValue(Integer.toHexString((int)value));
						len = Long.toString(value).length();
						len = len >= m ? len : m;
						break;
					case 'o':
						m = m > n ? m : n;
						hasCal = true;
						value = argIndex;
						len = Long.toOctalString(value).length();
						len = len >= m ? len : m;
						break;
					case 'x': case 'X':
						m = m > n ? m : n;
						hasCal = true;
						value = argIndex;
						len = Long.toHexString(value).length();
						len = len >= m ? len : m;
						break;
					case 'e': case 'E': case 'g': case 'G': //default format: I.XXXXXXE-XXX
						
						hasCal = true;
						if (!hasDot) { //such as %me or %mE, use the default format.
							len = m > 13 ? m : 13;
						} else { //such as %m.ne or %m.nE
							if (n == 0) { //format: IE-XXX
								len = m > 6 ? m : 6;
							} else { //format: I.XX...XXE-XXX "XX...XX" has n bytes
								len = 7+n;
								len = len > m ? len : m;
							}
						}
						
						break;
					case 'f':
						hasCal = true;
						value = argIndex;
						len = Long.toString(value).length(); //get the length of the integer part for the float number.
						
						if (!hasDot) { //not limit to the fractional part of the float number, such as "%mf"
							len += 7; //6 default bytes for the fractional part and 1 byte for the dot, such as ".XXXXXX"
							len = len > m ? len : m;
						} else {
							if (n == 0) {
								len = len > m ? len : m;
							} else {
								len += (n+1); //1 byte for the dot.
								len = len > m ? len : m;
							}
						}
						
						break;
					case 's':
						hasCal = true;
						len = getStringLength(argIndex);
						len = len > m ? len : m;
						break;
					case 'c':
						hasCal = true;
						len = m > 0 ? m : 1;
						break;
					case 'p':
						hasCal = true;
						len = m > 8 ? m : 8;
						break;
					default:
						break;
					}
					
					if (hasCal) {
						++curPos;
						totalLen += len;
						isStart = false;
						hasDot = false;
						m = n = 0;
						break;
					}
				}
			}
		}
		 
		return ++totalLen;//Add a byte to store the '\0'
	}
	
	/**
	 * Get the IntegerDomain for a specific constant string.
	 * @return
	 */
	public static long getConstStrLength(String string) {
		long totalLen = getConstStringLength(string);
	
		return ++totalLen;//add one byte for '\0';
	}
	
	/**
	 * Get the length for each control format string, such as "%5s%10d", it will return a list stores <5, 10>.
	 * -1 for default, such as "%s",  it return <-1>;flag = true "%5d" return 5,flag = false "%5d" return -1,
	 * @param string boolean
	 * @return
	 */
	public static List<Long> getFSVarsLenList(String string,boolean flag) {
		List<Long> lenList = new ArrayList<Long>();
		boolean isUnicode = false;
		
		if (string.startsWith("\"")) {
			string = string.substring(1);
		} else if (string.startsWith("L\"")) {
			string = string.substring(2);
			isUnicode = true;
		}
		if (string.endsWith("\"")) {
			string = string.substring(0, string.length()-1);
		}
		
		int strLen = string.length();
		boolean ignore = false; //if meets '*', set it to true. "%*ms"
		boolean isStart = false; //indicates the state for the state machine.
		
		for (int curPos = 0; curPos < strLen;) {
			char curChar = string.charAt(curPos);
			
			if (!isStart) {
				if (curChar == '%') {
					if (curPos+1 < strLen) {
						char nextChar = string.charAt(curPos+1);
						if (nextChar == '%') {
							curPos += 2;
						} else {
							isStart = true;
							++curPos;
						}
					}
				} else if (curChar == '\\') {
					curPos += 2;
				} else {
					++curPos;
				}
			} else {
				if (curChar == '*') {
					ignore = true;
					++curPos;
				} else {
					boolean hasM = false;
					int m = 0; //calculate 'm', such as "%ms".
					
					if (curChar >= '0' && curChar <= '9') {
						hasM = true;
						m = curChar - '0';
						++curPos;
						
						for (; curPos < strLen; ++curPos) {
							curChar = string.charAt(curPos);
							if (curChar >= '0' && curChar <= '9') {
								m = m*10 + (curChar-'0');
							} else {
								break;
							}
						}
					}
					
					if (curChar == '.') { //maybe "%m.nf". just ignore it.
						++curPos;
						
						for (; curPos < strLen; ++curPos) {
							curChar = string.charAt(curPos);
							if (curChar > '9' || curChar < '0') {
								break;
							}
						}
					}
					
					boolean isEndwithS = false; 
					for (; curPos < strLen; ++curPos) {
						curChar = string.charAt(curPos);
						if (curChar == 's') {
							isStart = false;
							isEndwithS = true;
							
							if (!ignore) {
								if (hasM) {
									++m;
									if (isUnicode) {
										m *= 2;
									}
									
									lenList.add(new Long(m));
								} else {
									lenList.add(new Long(-1));
								}
							}
							
							++curPos;
							ignore = false;
							
							break;
						} else if (curChar == '%') {
							if (!ignore) {
								lenList.add(new Long(-1));
							}
							
							isStart = false;
							ignore = false;
							isEndwithS = false;
							
							break;
						}else if(curChar == 'd'&&flag==true){//||curChar == 'o'||curChar == 'x'||curChar == 'u'
							isStart = false;
							isEndwithS = true;
							
							if (!ignore) {
								if (hasM) {
									++m;
									if (isUnicode) {
										m *= 2;
									}
									
									lenList.add(new Long(m));
								} else {
									lenList.add(new Long(-1));
								}
							}
							
							++curPos;
							ignore = false;
							
							break;
							
						}
					}
					if (curPos == strLen && !isEndwithS) {
						lenList.add(new Long(-1));
					}
					
				}
			}
		}
		
 		return lenList;
	}

	/**
	 * For test.
	 */
	public static void main(String[] args) {
		System.out.println(Double.SIZE);
		//String string = "\"%*s%10s%4d%15s%d%10.1f%d%I64d%s%111s\"";
		String string = "%i:12:%c ";//"L\"%10s%d%*s%*10d%5s\"";
		List<Long> lenList = BOHelper.getFSVarsLenList(string,true);
		//System.out.println("\""+"1111"+"\"");
		for (Long len : lenList) {
			System.out.println(len);
		}
		
	}
}

