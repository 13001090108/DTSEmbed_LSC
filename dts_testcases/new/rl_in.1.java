// RL_IN
public class test {
	public Image loadImage(String strUrl) {
		try {
		URL url = new URL(¡°http://www.baidu.com¡±);
		return new Image(Display.getCurrent(), url.openStream());
	} catch (Exception e) {
		return null;
	}
	}
}
