package softtest.domain.c.interval;

public enum PointerValue {
	/** 只能取null */
	NULL,
	/** 不可能为null */
	NOTNULL,
	/** null和非null都可能 */
	NULL_OR_NOTNULL,
	/** null和非null都不能取，矛盾 */
	EMPTY,
	/** 未知，用于表示初始化 */
	UNKOWN
}