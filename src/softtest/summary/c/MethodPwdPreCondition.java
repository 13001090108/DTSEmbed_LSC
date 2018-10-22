package softtest.summary.c;

/**
 * The entity to record the function precondition.
 * @author liuyan
 *
 */
public class MethodPwdPreCondition extends MethodFeatureComplement {
	
	private final static String METHOD_PWDFILE_RELATED_PRECONDITION = "method_pwdfile_related_precondition";
	
	private int index;
	private String subType;
	private String from;

	public int getIndex() {
		return index;
	}

	public String getSubType() {
		return subType;
	}

	public void setSubType(String subType) {
		this.subType = subType;
	}

	public String getFrom() {
		return from;
	}

	public void setFrom(String from) {
		this.from = from;
	}

	public void setIndex(int index) {
		this.index = index;
	}

	public MethodPwdPreCondition() {
		super(METHOD_PWDFILE_RELATED_PRECONDITION);
	}
}
