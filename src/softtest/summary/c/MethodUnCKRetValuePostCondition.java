package softtest.summary.c;

/**
 * <p>
 * Record information of the functions witch must be checked their return values.
 * </p>
 * @author liuyan
 *
 */
public class MethodUnCKRetValuePostCondition extends MethodFeatureComplement {
	
	private final static String METHOD_UNCK_RET_VALUE_POSTCONDITION = "method_unck_ret_value_feature";

	public MethodUnCKRetValuePostCondition() {
		super(METHOD_UNCK_RET_VALUE_POSTCONDITION);
	}
}
