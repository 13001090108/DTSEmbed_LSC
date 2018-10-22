package softtest.rules.gcc.safety.BO;

public enum BOType {
	BUFFERCOPY, 	// buffer, copy from source to dest
	FORMATSTRING, 	// format string like printf,
	FORMATIN,     	// scanf
	FORBIDDEN		// gets
}
