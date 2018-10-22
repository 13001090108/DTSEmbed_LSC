package softtest.cfg.c;

import java.io.Serializable;

/** VexNode Edge Graph的抽象基类 */
public abstract class Element implements Serializable {
	/** 访问者模式的accept方法 */
	public abstract void accept(GraphVisitor visitor, Object data);
}
