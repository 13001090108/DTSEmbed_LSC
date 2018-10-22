package softtest.summary.gcc.fault;

public enum IAOType {
	NO_ZERO,	//不能为0
	NO_BELOW_ZERO, //大于等于0
	ABOVE_ZERO,	//大于0
	TRI_LIMIT, //反三角函数参数限制[-1,1]
}
