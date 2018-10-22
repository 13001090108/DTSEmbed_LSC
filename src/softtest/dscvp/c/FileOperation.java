package softtest.dscvp.c; 

import java.io.BufferedReader;  
import java.io.BufferedWriter;
import java.io.File;  
import java.io.FileOutputStream;  
import java.io.FileReader;  
import java.io.FileWriter;
import java.io.IOException;
import java.io.RandomAccessFile;  
  
public class FileOperation {  
    public static boolean writeTxtFile(String content,File fileName)throws Exception{ 
	 FileWriter writer=new FileWriter(fileName.getPath());
	 System.out.println("name: " + fileName.getPath());
	 try{
		 //使用这个构造函数时，如果存在kuka.txt文件，
		 //则先把这个文件给删除掉，然后创建新的kuka.txt
		 writer.write(content);
		 writer.write("hello");
     } catch (IOException e){
           e.printStackTrace();
     }finally{
         writer.close();
     }
	return true;   
 }
} 