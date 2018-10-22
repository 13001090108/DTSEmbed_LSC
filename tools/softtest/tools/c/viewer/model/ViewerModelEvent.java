package softtest.tools.c.viewer.model;

/**
 * The event which will be sent every time the model changes <p/> <p/> <p/> <p/>
 * <p/> Note: the instances will be immutable <p/>
 * </p>
 * 
 * @author Boris Gruschko ( boris at gruschko.org )
 * @version $Id: ViewerModelEvent.java,v 1.3 2010/04/13 08:52:15 liuli Exp $
 */
public class ViewerModelEvent
{
	/**
	 * reason in the case of code recompilation
	 */
	public static final int CODE_RECOMPILED = 1;
	/**
	 * reason in the case of node selection
	 */
	public static final int NODE_SELECTED = 2;
	/**
	 * reason in the case of path extension
	 */
	public static final int PATH_EXPRESSION_APPENDED = 3;
	/**
	 * reason in the case of path expression evaluation
	 */
	public static final int PATH_EXPRESSION_EVALUATED = 4;
	
	public static final int IMAGE_REPAINT = 5;
	//liuli 2010.4.13 µ÷ÓÃÍ¼Ìí¼Ó
	public static final int IMAGE_CG_REPAINT = 6;
	
	private Object source;
	private int reason;
	private Object parameter;

	/**
	 * Creates an event
	 * 
	 * @param source
	 *            event's source
	 * @param reason
	 *            event's reason
	 */
	public ViewerModelEvent(Object source, int reason)
	{
		this(source, reason, null);
	}

	/**
	 * Creates an event
	 * 
	 * @param source
	 *            event's source
	 * @param reason
	 *            event's reason
	 * @param parameter
	 *            parameter object
	 */
	public ViewerModelEvent(Object source, int reason, Object parameter)
	{
		this.source = source;
		this.reason = reason;
		this.parameter = parameter;
	}

	public int getReason()
	{
		return reason;
	}

	public Object getSource()
	{
		return source;
	}

	public Object getParameter()
	{
		return parameter;
	}
}
