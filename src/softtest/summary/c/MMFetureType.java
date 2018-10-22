package softtest.summary.c;

/**
 * C/C++中函数关于内存管理副作用的类型
 * 包括C语言中的malloc和free，以及C++中的new, delete, 以及new[], delete[]
 */
public enum MMFetureType {
	MALLOC,
	CALLOC,
	FREE,
	NEW,
	DELETE,
	NEW_ARRAY,
	DELETE_ARRAY,
	GLOABAL_FREE
}
