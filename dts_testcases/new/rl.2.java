//ServerSocketChannel资源识别

import java.nio.channels.ServerSocketChannel;
public class test {
  public static void main(String[] args)
  {
	try {
	  	final ServerSocketChannel ssc = ServerSocketChannel.open();
	  } catch (Throwable e) {
	  	return;
	  }

  }
}
