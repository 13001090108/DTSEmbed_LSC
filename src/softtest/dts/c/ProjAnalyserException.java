package softtest.dts.c;

public class ProjAnalyserException extends Exception {
	
	public ProjAnalyserException(String msg) {
		super(msg);
	}
	
	public ProjAnalyserException(Throwable cause, String msg) {
		super(msg, cause);
	}
}