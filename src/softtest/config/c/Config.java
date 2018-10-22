package softtest.config.c;


public class Config
{
	/**增加域敏感分析开关，用来检测域分析效率 */
	public static boolean Field=true;
	
	//dyk 20130624 扩充变量的层数
	public static int VAR_LEVEL = 5;
	
	/**域敏感分析中数组大小上限 */
	public static int MaxArray=10;
	
	/**为了提高华为代码的测试效率，如果只分析华为的规则类，可以跳过定义使用链和区间分析的步骤 */
	
	public static boolean HW_RULES_CUT=false;

	/**在状态机迭代计算时,true表示每访问完一个节点,就试图清空当前节点的状态机实例集合，以提高分析效率 */
	public static boolean FSM_REMOVE_PER_NODE=true;
	
	/**用于监控状态机分析时，各个状态机的创建及销毁情况，默认为false */
	public static boolean FSM_STATISTIC=false; 
	
	/**是否进行不识别串替换*/
	public static boolean FILEREPLACE = true;
	
	/**是否对预处理后的.i中间文件进行化简，如去除重复的头文件展开 */
	public static boolean InterFile_Simplified = false;

	/**输出文件内函数相关信息的文件路径 */
		//public static String TRACEPATH="C:\\temp";
	public static String TRACEPATH="C:\\temp";
	/**区分GCC开发环境(不同开发环境所得到的中间文件路径名不一致） liuli：2010.8.12
	 * <p>GCC_TYPE=0 表示开发环境为MinGW</p>
	 * <p>GCC_TYPE=1 表示开发环境为cygwin</p>
	 */
	public static  int GCC_TYPE=1;
	
	/** 为了识别某函数是否为库函数，添加系统头文件的路径，如果为多路径则以分号分开*/
	public static String LIB_HEADER_PATH="/usr/include;/usr/local/include;";
	
	/** 是否输出函数的控制流图，状态机图 */
	public static boolean TRACE = false;
	
	public static boolean TRACECFG = false;
	
	/**是否输出文件调用关系图*/  //qian-2011-07-27
	public static boolean TRACE_FCG = false;
	
	/**是否是出全局函数调用关系图*/ //qian-2011-07-27
	public static boolean TRACE_ICG = false;
	
	/** 是否自动关闭progFrame窗口 */
	public static boolean AUTOCLOSE = false;

	/**0:路径不敏感 1：相同状态合并2：不允许合并*/
	public static int PATH_SENSITIVE=2;
	/** 为避免路径敏感分析时路径爆炸，设置路径数的上限*/
	public static int PATH_LIMIT = 10000000;
	
	/** 分析超时限制，单位为毫秒 */
	public static long TIMEOUT = 1200000;
	
	/**生成语法树时的超时限制 */
	public static long ASTTREE_TIMEOUT=1200000;

	/**在路径敏感分析前，首先判断当前控制流图的节点个数，如果超过了该上限，则为了提高分析效率不再进行路径敏感分析 */
	public static int MAXVEXNODENUM=100;

	/**由于中间文件.i中的条件判断节点可能非常复杂（宏展开？），导致语法树层次比较多，在区间分析时如果超过了该深度
	 * 上限，则不再分析此类条件判断节点 */
	public static int MAXASTTREEDEPTH=50;
	
	/**预处理之后中间文件的存放位置*/
	public static String PRETREAT_DIR = "temp";
	
	/**zys:2010.5.17 临时开关：用于循环处理的widening/narrowing改进*/
	public static boolean LOOPCAL=true;
	
	/**为保证循环迭代可以终止，设定一个迭代的上限 */
	public static final int LOOPNUM=5;
	
	/**为保证循环迭代的快速处理，设定一个循环处理的层次 */
	public static int LOOPLAYER=2;
	
	/**zys <p>在用viewer工具调试时，将本变量设置为false，不进行行号映射
	 * （当对预处理之后的.i中间文件分析时有效）</p>*/
	public static boolean COMPUTE_LINE_NUM=true;
	
	/** zys	是否做全局函数调用分析*/
	public static final boolean INTER_METHOD_TRACE = false;

	/** 加载生成库函数的摘要信息*/
	public static final boolean USE_SUMMARY = true;
	
	//dyk 库函数没有人工摘要，则返回值为全区间
	public static final boolean LIB_NOSUMMARY_NPD=true;
	
	/**是否通过序列号进行注册 */
	public static final boolean REGISTER = false;
	
	/** 是否使用授权文件来注册 */
	public static final boolean FILE_LICENSE = false;

	/**是否通过加密锁进行加密*/
	public static  final boolean LOCK = false;
	
	/** 是否为网络版 */
	public static final boolean NETWORK_LOCK = false;
	public static final Nlock_size NLOCK_SIZE = Nlock_size.S54;  //默认为S54
	
	/** 是否为服务器版 */        
	public static final boolean ISSERVER=false;

	/** 是否有使用次数的限定*/
	public static final boolean PHASE_REGISTER = false;
	public static final int PHASE_NUMUBER = 10;
	
	public static final boolean ISTRIAL=false;
	/**测试版每类IP输出比例*/
	public static final double PERCENT=20;
	
	/**测试版每类IP最大输出数目*/
	public static final int MAXIP=10;
	

	/** 是否重新编译规则的动作文件 */
	public static boolean COMPILEFSM = false;

	/** 是否保留C预处理文件*/
	public static boolean DELETE_PRETREAT_FILES = false;
	
	/** 用于计算某数据类型的字节数（sizeof）*/
	public static int INT_SIZE=4;
	
	/** 计算union的字节数时，默认的#pragma pack 1*/
	public static int PACK_SIZE=1;


	/**zys:判断当前是否是回归测试用例生成模式，如果true则测试结果不写数据库*/
	public static boolean REGRESS_RULE_TEST=false;

	public static String version= "DTSGCC7";
	
	/**控制流图打印时，是否打印区间信息 */
	public static boolean DUMP_DOMAIN=false;
	
	/**控制流图打印时，是否打印符号运算信息 */
	public static boolean DUMP_SYMBOL=false;
	/**区分分析类型 liuli：2010.6.25
	 * ANALYSIS_P为真表示为工程分析
	 * ANALYSIS_I为真表示为中间文件分析
	 * ANALYSIS_R为真表示为源文件分析*/
	public static boolean ANALYSIS_P=false;
	public static boolean ANALYSIS_I=false;
	public static boolean ANALYSIS_R=false;
	
	public final static int LANG_ENGLISH = 0;
	public final static int LANG_CHINESE = 1;

	/**xwt 2011.11.3   	是否输出非缺陷模式数据库*/


	public static boolean TRIAL_OUTPUT_ALL = false;
	
	/**zys 2011.6.24	在对符号运算的功能进行回归测试时softtest.test.c.symbolic.TestSymbolic.java，不生成变量序号 */
	public static boolean TEST_SYMBOLIC = false;
	
	public static int DTS_LANGUAGE = LANG_CHINESE;
	//对于unknow的处理，为true时unknow并上任何其他值都为unknow
	public static boolean DOMAIN_CONSERVATIVE=true;
	public static boolean USEUNKNOWN = true;
	
	//stat数据库密码
	public static String DB_STAT_PASSWORD = "741852963";
	
	//被测工程采用的是否是HPC编译器
	public static boolean isHPC=false;
	
	public static boolean SHOW_DIALOG = true;
	
	/*-----------日志log配置信息------------*/
	//log control begin
	
//	public static String LOG_FILE=".\\log\\c.log";
	public static String LOG_FILE=".\\log\\";
	public static String FILE;
	/** 是否在log中记录每一分析步骤的耗时*/
	public static boolean STEP_TIME_TRACE=false;
	
	//是否输出分析时的异常信息
	public static boolean PRINT_LOG_ERROR=true;
	
	///** true表示日志文件删除后重新生成,即覆盖;false表示在原日志最后续写*/
	public static boolean LOG_REPLACE=true;
	
	/**是否跳过预处理过程，当分析中间文件时，将开关设置为true，可以跳过预处理分析，直接进行分析，注意，分析源文件时，将开关必须设置为false*/
	public static boolean SKIP_PREANALYSIS=false;
	/**是否查看预处理中生成抽象语法树开关，将开关设置为true，可以查看预处理中生成抽象语法树的过程*/
	public static boolean PreAnalysisASTRoot=false;
	/**是否查看预处理中生成符号表开关，将开关设置为true，可以查看预处理中生成符号表的过程*/
	public static boolean PreAnalysisSymbolTable=false;
	/**是否查看预处理中全局函数调用分析开关，将开关设置为true，可以查看预处理中全局函数调用分析的过程*/
	public static boolean PreAnalysisInterMethodVisitor=false;
	
	/**是否查看文件分析顺序开关，将开关设置为true，可以查看文件的分析顺序，分析顺序是按照字母顺序分析或者按照拓扑排序*/
	public static boolean FileAnalysisOrder=true;
	
	/**是否跳过函数分析日志过程开关，将开关设置为true，可以跳过函数分析日志过程，即1/2/3/4/5/6开关设置无效，设置为false， 可以查看函数分析具体过程*/
	public static boolean SKIP_METHODANALYSIS=true;
	/**1 是否查看函数分析中生成抽象语法树开关，将开关设置为true，可以查看函数中生成抽象语法树的过程*/
	public static boolean MethodAnalysisASTRoot=false;
	/**2 是否查看函数分析中生成符号表开关，将开关设置为true，可以查看函数分析中生成符号表的过程*/
	public static boolean MethodAnalysisSymbolTable=false;
	/**3 是否查看函数分析中全局函数调用分析开关，将开关设置为true，可以查看函数分析中全局函数调用分析的过程*/		
	public static boolean MethodAnalysisInterMethodVisitor=false;
	/**4 是否查看函数分析中控制流图分析开关，将开关设置为true，可以查看函数分析中控制流图分析的过程*/
	public static boolean MethodAnalysisControlFlowVisitor=false;
	/**5 是否查看函数分析中计算定义使用链分析开关，将开关设置为true，可以查看函数分析中定义使用链分析的过程*/
	public static boolean MethodAnalysisDUAnalysisVisitor=false;
	/**6 是否查看函数分析中区间分析开关，将开关设置为true，可以查看函数分析中区间分析的过程*/
	public static boolean MethodAnalysisDomainVisitor=false;
	
	/**是否查看实例分析阶段开关，将开关设置为true，可以查看实例分析的结果日志过程*/
	public static boolean FSMInstanceAnalysis=false;
	
	
	/**是否查看加载的状态机，查看：true 不查看：false*/
	public static boolean LoadFSM = true;
	//这些开关需要调用图形绘制工具，所以这些开关的生效需要安装该工具：Graphviz
	//Graphviz begin
	/**是否输出全局函数调用关系*/
	public static boolean GlobalFunctionCall = false;
	/**是否输出全局文件依赖关系*/
	public static boolean GlobalFileCallRelation = false;
	/**是否输出文件内函数调用关系*/
	public static boolean CallGraph = false;
	/**是否输出控制流图(DU定义使用链)*/
	public static boolean DU = false;
	/**是否输出控制流图(区间分析)*/
	public static boolean Domain = false;
	/**是否输出状态机转换过程*/
	public static boolean StateTransition = false;
	
	//Graphviz end
	
	//log control end
	//added by cmershen,是否聚类
	public static boolean Cluster = false;
}
