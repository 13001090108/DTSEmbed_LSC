package softtest.tools.c.logswitch;  

import java.io.*;
import java.awt.event.WindowAdapter;
import java.awt.event.WindowEvent;

import javax.swing.JFrame;  
import javax.swing.JScrollPane;  
import javax.swing.JTree;  
import javax.swing.tree.DefaultTreeModel;  
 
public class GCCSwitch   
{  
    public static void main(String[] args)  
    {  
        JFrame frame = new JFrame("GCC日志开关");  
        frame.setBounds(200, 200, 420, 550);  
        
        JTree tree = new JTree();  
        final CheckBoxTreeNode rootNode = new CheckBoxTreeNode("日志总开关");  
        final CheckBoxTreeNode node1 = new CheckBoxTreeNode("预处理过程"); 
        final CheckBoxTreeNode node1_1 = new CheckBoxTreeNode("生成抽象语法树");  
        final CheckBoxTreeNode node1_2 = new CheckBoxTreeNode("生成符号表");  
        final CheckBoxTreeNode node1_3 = new CheckBoxTreeNode("全局函数调用分析");     
        final CheckBoxTreeNode node2 = new CheckBoxTreeNode("分析过程");
        final CheckBoxTreeNode node2_1 = new CheckBoxTreeNode("文件分析顺序");  
        final CheckBoxTreeNode node2_2 = new CheckBoxTreeNode("全局函数调用关系"); 
        final CheckBoxTreeNode node2_3 = new CheckBoxTreeNode("全局文件依赖关系"); 
          
        final CheckBoxTreeNode node2_4 = new CheckBoxTreeNode("生成抽象语法树"); 
        final CheckBoxTreeNode node2_5 = new CheckBoxTreeNode("生成符号表"); 
        final CheckBoxTreeNode node2_6 = new CheckBoxTreeNode("文件内全局函数调用分析");
        final CheckBoxTreeNode node2_6_1 = new CheckBoxTreeNode("输出文件内函数调用关系");
        final CheckBoxTreeNode node2_7 = new CheckBoxTreeNode("控制流图分析");
        final CheckBoxTreeNode node2_8 = new CheckBoxTreeNode("计算定义使用链分析");
        final CheckBoxTreeNode node2_8_1 = new CheckBoxTreeNode("输出定义使用链过程");
        final CheckBoxTreeNode node2_9 = new CheckBoxTreeNode("区间分析");
        final CheckBoxTreeNode node2_9_1 = new CheckBoxTreeNode("输出区间分析过程");
        final CheckBoxTreeNode node2_10 = new CheckBoxTreeNode("实例分析");
        final CheckBoxTreeNode node2_10_1 = new CheckBoxTreeNode("状态机转换");
        
        node1.add(node1_1);  
        node1.add(node1_2);
        node1.add(node1_3);
        node2.add(node2_1);
        node2.add(node2_2);
        node2.add(node2_3);
        node2.add(node2_4);
        node2.add(node2_5);
        node2.add(node2_6);
        node2.add(node2_7);
        node2.add(node2_8);
        node2.add(node2_9);
        node2.add(node2_10);
        
        node2_6.add(node2_6_1);
        node2_8.add(node2_8_1);
        node2_9.add(node2_9_1);
        node2_10.add(node2_10_1);
       
        rootNode.add(node1);  
        rootNode.add(node2); 
        

        //rootNode.setSelected(true);
        
        DefaultTreeModel model = new DefaultTreeModel(rootNode);  
        
        tree.addMouseListener(new CheckBoxTreeNodeSelectionListener());  
        tree.setModel(model);  
        tree.setCellRenderer(new CheckBoxTreeCellRenderer());  
        JScrollPane scroll = new JScrollPane(tree);  
        scroll.setBounds(0, 0, 300, 320);  
        frame.getContentPane().add(scroll);  
       
        frame.setDefaultCloseOperation(JFrame.EXIT_ON_CLOSE);  
        frame.setVisible(true);
        
        frame.addWindowListener(new WindowAdapter() {
        	public void windowClosing(WindowEvent arg0){
        		boolean[] WTF;
        		WTF = new boolean[25];
        		WTF[0]=rootNode.isSelected();
        		WTF[1]=!(node1.isSelected());
        		WTF[2]=node1_1.isSelected();
        		WTF[3]=node1_2.isSelected();
        		WTF[4]=node1_3.isSelected();
        		WTF[5]=!(node2.isSelected());
        		WTF[6]=node2_1.isSelected();
        		WTF[7]=node2_2.isSelected();
        		WTF[8]=node2_3.isSelected();
        		WTF[9]=node2_4.isSelected();
        		WTF[10]=node2_5.isSelected();
        		WTF[11]=node2_6.isSelected();
        		WTF[12]=node2_6_1.isSelected();
        		WTF[13]=node2_7.isSelected();
        		WTF[14]=node2_8.isSelected();
        		WTF[15]=node2_8_1.isSelected();
        		WTF[16]=node2_9.isSelected();
        		WTF[17]=node2_9_1.isSelected();
        		WTF[18]=node2_10.isSelected();
        		WTF[19]=node2_10_1.isSelected();
        		WriteToFile(WTF);
        	}  	
		});
    }  
    
    public static void WriteToFile(boolean[] x){
    	File file = new File("config\\config.ini");
    	//String[] arr = new String[10];//定义arr数组，存储能在界面上修改的开关信息
    	String s = "";//定义s字符串，存储不在界面上修改的开关信息
    	String temp = "";//定义一个temp临时变量，存储正在读取的上一行信息
    	if(file.exists()){
    		try 
    		{
    			BufferedReader reader = new BufferedReader(new FileReader(
						file));
				String config;
				
				while((config = reader.readLine())!= null){
					if(config.startsWith("#")){
						temp = config;//temp将以#开头的那一行的信息全部保存下来
						continue;
					}
					else if(config.length() == 0){
						temp = "";//遇到空行就将temp重新清空
						//s = s + "\r\n";//往s中增加一个空行
						continue;
					}
					else if(config.startsWith("-SKIP_PREANALYSIS")){
						temp = "";//遇到能在界面上操作的开关，就将temp清空，不保存这些信息
						continue;
					}
					else if(config.startsWith("-PreAnalysisASTRoot")){
						temp = "";//同上
						continue;
					}
					else if(config.startsWith("-PreAnalysisSymbolTable")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-PreAnalysisInterMethodVisitor")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-SKIP_METHODANALYSIS")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-FileAnalysisOrder")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-GlobalFunctionCall")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-GlobalFileCallRelation")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-MethodAnalysisASTRoot")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-MethodAnalysisSymbolTable")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-MethodAnalysisInterMethodVisitor")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-CallGraph")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-MethodAnalysisControlFlowVisitor")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-MethodAnalysisDUAnalysisVisitor")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-DU")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-MethodAnalysisDomainVisitor")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-Domain")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-FSMInstanceAnalysis")){
						temp = "";
						continue;
					}
					else if(config.startsWith("-StateTransition")){
						temp = "";
						continue;
					}
					else {//其他情况就是需要保存信息的开关
						temp = temp + "\r\n" + config ;
						s= s + temp + "\r\n\r\n";//将这些信息增加到s中并增加一个空行
						temp = "";//清空temp
					}
				}
				reader.close();
    		}    
    		catch (Exception e)
			{
				System.err.println("Error in reading the config file.");
			}
    	}
    	try
    	{
    		FileWriter fw = new FileWriter(file,false);
    		
    		fw.write(s);//将s中保存的信息重新写入到文件中
    		
    		fw.write("#是否跳过预处理过程\r\n");
   			fw.write("-SKIP_PREANALYSIS "+x[1]+"\r\n\r\n");
   			fw.write("#是否查看预处理中生成抽象语法树\r\n");
   			fw.write("-PreAnalysisASTRoot "+x[2]+"\r\n\r\n");
   			fw.write("#是否查看预处理中生成符号表\r\n");
   			fw.write("-PreAnalysisSymbolTable "+x[3]+"\r\n\r\n");
   			fw.write("#是否查看预处理中全局函数调用分析\r\n");
   			fw.write("-PreAnalysisInterMethodVisitor "+x[4]+"\r\n\r\n");
   			fw.write("#是否跳过函数分析日志过程\r\n");
   			fw.write("-SKIP_METHODANALYSIS "+x[5]+"\r\n\r\n");
   			fw.write("#是否查看文件分析顺序\r\n");
   			fw.write("-FileAnalysisOrder "+x[6]+"\r\n\r\n");
   			fw.write("#是否输出全局函数调用关系\r\n");
   			fw.write("-GlobalFunctionCall "+x[7]+"\r\n\r\n");
   			fw.write("#是否输出全局文件依赖关系\r\n");
   			fw.write("-GlobalFileCallRelation "+x[8]+"\r\n\r\n");
   			fw.write("#是否查看函数分析中生成抽象语法树\r\n");
   			fw.write("-MethodAnalysisASTRoot "+x[9]+"\r\n\r\n");
   			fw.write("#是否查看函数分析中生成符号表\r\n");
   			fw.write("-MethodAnalysisSymbolTable "+x[10]+"\r\n\r\n");
   			fw.write("#是否查看函数分析中全局函数调用分析\r\n");
   			fw.write("-MethodAnalysisInterMethodVisitor "+x[11]+"\r\n\r\n");
   			fw.write("#是否输出文件内函数调用关系\r\n");
   			fw.write("-CallGraph "+x[12]+"\r\n\r\n");
   			fw.write("#是否查看函数分析中控制流图分析\r\n");
   			fw.write("-MethodAnalysisControlFlowVisitor "+x[13]+"\r\n\r\n");
   			fw.write("#是否查看函数分析中计算定义使用链分析\r\n");
   			fw.write("-MethodAnalysisDUAnalysisVisitor "+x[14]+"\r\n\r\n");
   			fw.write("#是否输出控制流图(DU定义使用链)\r\n");
   			fw.write("-DU "+x[15]+"\r\n\r\n");
   			fw.write("#是否查看函数分析中区间分析\r\n");
   			fw.write("-MethodAnalysisDomainVisitor "+x[16]+"\r\n\r\n");
   			fw.write("#是否输出控制流图(区间分析)\r\n");
   			fw.write("-Domain "+x[17]+"\r\n\r\n");
   			fw.write("#是否查看实例分析阶段\r\n");
   			fw.write("-FSMInstanceAnalysis "+x[18]+"\r\n\r\n");
   			fw.write("#是否输出状态机转换过程\r\n");
   			fw.write("-StateTransition "+x[19]+"");
   			
   			fw.flush();
   			fw.close();
   		} catch (FileNotFoundException e)
    	{
    		e.printStackTrace();
    	} catch (IOException e)
    	{
    		e.printStackTrace();
    	}
    }
} 


