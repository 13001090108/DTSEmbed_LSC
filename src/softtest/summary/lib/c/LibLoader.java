package softtest.summary.lib.c;

import java.io.FileInputStream;
import java.io.InputStream;
import java.util.HashSet;
import java.util.Set;

import javax.xml.parsers.DocumentBuilder;
import javax.xml.parsers.DocumentBuilderFactory;

import org.w3c.dom.Document;
import org.w3c.dom.Element;
import org.w3c.dom.Node;
import org.w3c.dom.NodeList;

import softtest.domain.c.interval.*;
import softtest.summary.c.MethodFeatureType;
import softtest.summary.lib.c.LibMethodDespAPIAbuse;
import softtest.summary.lib.c.LibMethodDespUnCKRetValue;
import softtest.symboltable.c.Type.CType_AllocType;

/**
 * 
 * 从XML配置文件中加载库函数函数摘要信息
 * 
 * @author 祁鹏
 * 
 */
public class LibLoader
{

	/**
	 * <p>
	 * 加载XML描述文件中的库函数摘要信息
	 * </p>
	 * 
	 * @param path
	 *            库函数摘要描述文件路径
	 * @return 成功加载的库函数摘要集合
	 */
	public static Set<LibMethodSummary> loadLibSummarys(String path)
	{
		Set<LibMethodSummary> libSet = new HashSet<LibMethodSummary>();
		DocumentBuilderFactory domfac = DocumentBuilderFactory.newInstance();
		try
		{
			DocumentBuilder dombuilder = domfac.newDocumentBuilder();
			InputStream is = new FileInputStream(path);
			Document doc = dombuilder.parse(is);
			Element root = doc.getDocumentElement();
			if (root == null)
			{
				throw new RuntimeException(
						"This is not a legal lib summary define file.");
			}
			NodeList nodes = root.getChildNodes();
			for (int i = 0; i < nodes.getLength(); i++)
			{
				Node node = nodes.item(i);
				if (node.getNodeName().equals("Method"))
				{
					loadLibSummary(libSet, node);
				}
			}
		}
		catch (Exception e)
		{
			throw new RuntimeException(
					"Errror in loading the lib methods summarys", e);
		}
		return libSet;
	}

	/**
	 * 加载库函数摘要信息，包括前置约束，特征信息，返回值区间等
	 * 
	 * @param libSet
	 * @param node
	 */
	public static void loadLibSummary(Set<LibMethodSummary> libSet, Node node)
	{
		try
		{
			Node methodNameNode = node.getAttributes().getNamedItem("name");
			Node libNameNode = node.getAttributes().getNamedItem("libPos");
			Node signNode = node.getAttributes().getNamedItem("signature");
			if (methodNameNode != null && libNameNode != null
					&& signNode != null)
			{
				LibMethodSummary libMethod = new LibMethodSummary(libNameNode
						.getNodeValue(), methodNameNode.getNodeValue(),
						signNode.getNodeValue());
				NodeList nodes = node.getChildNodes();
				for (int i = 0; i < nodes.getLength(); i++)
				{
					Node item = nodes.item(i);
					if (item.getNodeName().equals("Feature"))
					{
						loadFetures(item, libMethod);
					}
					else
						if (item.getNodeName().equals("Return"))
						{
							Node typeNode = item.getAttributes().getNamedItem(
									"type");
							Node valueNode = item.getAttributes().getNamedItem(
									"value");
							if (typeNode != null && valueNode != null)
							{
								Domain retDomain = loadDomain(typeNode
										.getNodeValue(), valueNode
										.getNodeValue());
								if (retDomain != null)
								{
									libMethod.setRetDomain(retDomain);
								}
							}
						}
						else
							if (item.getNodeName().equals("Allocate"))
							{
								Node typeNode = item.getAttributes()
										.getNamedItem("type");
								Node valueNode = item.getAttributes()
										.getNamedItem("value");
								if (typeNode != null && valueNode != null)
								{
									boolean isAllocate = loadIsAllocate(valueNode
											.getNodeValue());
									libMethod.setIsAllocate(isAllocate);
									// 同步retDomain
									// add by zhouhb 2010/10/19
									if (isAllocate)
									{
										PointerDomain res = (PointerDomain) libMethod
												.getRetDomain();
										res.Type.add(CType_AllocType.heapType);
									}

								}
							}
				}
				libSet.add(libMethod);
			}
		}
		catch (Exception e)
		{
			throw new RuntimeException(
					"This is illegal lib method summary node", e);
		}
	}

	/**
	 * 加载库函数特征信息
	 * 
	 * @param node
	 * @param libMethod
	 */
	public static void loadFetures(Node node, LibMethodSummary libMethod)
	{
		Node typeNode = node.getAttributes().getNamedItem("type");
		if (typeNode != null)
		{
			if (typeNode.getNodeValue().equals("PRECOND_NPD"))
			{
				Node valueNode = node.getAttributes().getNamedItem("value");
				if (valueNode != null)
				{
					Integer value = Integer.valueOf(valueNode.getNodeValue());
					libMethod.addFeature(new LibMethodDespPrecondNpd(
							MethodFeatureType.PRECOND_NPD, value));
				}
			}/*
			else if (typeNode.getNodeValue().equals("TD_INPUT")) { 
				 Node valueNode = node.getAttributes().getNamedItem("value"); 
				 if(valueNode != null) { 
					 libMethod.addFeature(new LibMethodDespTdIn(MethodFeatureType.FEATURE_TDIN,
							 valueNode.getNodeValue())); 
					 } 
			}
			 else if(typeNode.getNodeValue().equals("TD_USE")) {//加载TD_USE库函数的函数摘要
				 Node valueNode = node.getAttributes().getNamedItem("value"); 
				 Node srcIndex = node.getAttributes().getNamedItem("srcIndex"); 
				 Node beginPara = node.getAttributes().getNamedItem("beginPara");//变参的情况下，变参的起始位置
				 Node retIndex = node.getAttributes().getNamedItem("isReturn");//参数导致返回值污染型如strtol, modified by 姚欣洪 2009.7.15 
				 if (valueNode != null && srcIndex != null && beginPara != null && retIndex != null) {
					libMethod.addFeature(new LibMethodDespTduse(MethodFeatureType.FEATURE_TDUSE,
					valueNode.getNodeValue(), srcIndex.getNodeValue(),
					beginPara.getNodeValue(), retIndex.getNodeValue())); 
					} 
				 }
				 */
			else if (typeNode.getNodeValue().equals("API_ABUSE")) {
				Node descNode = node.getAttributes().getNamedItem("Description");
				Node rankNode = node.getAttributes().getNamedItem("Rank");
				
				if (descNode != null && rankNode != null) {
					libMethod.addFeature(new LibMethodDespAPIAbuse(MethodFeatureType.API_ABUSE, descNode.getNodeValue(), rankNode.getNodeValue()));
				}
			}else if (typeNode.getNodeValue().equals("UNCK_RET_VALUE")) {
				Node descNode = node.getAttributes().getNamedItem("Description");
				Node rankNode = node.getAttributes().getNamedItem("Rank");
				
				if (descNode != null && rankNode != null) {
					libMethod.addFeature(new LibMethodDespUnCKRetValue(MethodFeatureType.UNCK_RET_VALUE, descNode.getNodeValue(), rankNode.getNodeValue()));
				}
			}			
			else
				if (typeNode.getNodeValue().equals("BO_PRECON"))
				{// 加载BO库函数的函数摘要
					Node subType = node.getAttributes().getNamedItem("subtype");
					Node bufIndex = node.getAttributes().getNamedItem(
							"bufIndex");
					Node srcIndex = node.getAttributes().getNamedItem(
							"srcIndex");
					Node limitLen = node.getAttributes().getNamedItem(
							"limitLen");
					Node needNull = node.getAttributes().getNamedItem(
							"needNull");

					if (subType != null && bufIndex != null && srcIndex != null
							&& limitLen != null && needNull != null)
					{
						boolean need = false;
						if (needNull.getNodeValue().equals("true"))
						{
							need = true;
						}
						else
						{
							need = false;
						}

						libMethod.addFeature(new LibMethodDespBo(
								MethodFeatureType.BO_PRECON, subType
										.getNodeValue(), bufIndex
										.getNodeValue(), srcIndex
										.getNodeValue(), limitLen
										.getNodeValue(), need));
					}
				}/*
				 * else if (typeNode.getNodeValue().equals("TD_PROPA")) { Node
				 * srcIndexNode = node.getAttributes().getNamedItem("srcIndex");
				 * Node dstIndexNode =
				 * node.getAttributes().getNamedItem("dstIndex"); Node
				 * beginParaNode =
				 * node.getAttributes().getNamedItem("beginPara"); Node
				 * isReturnNode = node.getAttributes().getNamedItem("isReturn");
				 * 
				 * if (srcIndexNode != null && dstIndexNode != null &&
				 * beginParaNode != null && isReturnNode != null) { boolean
				 * isReturn = false, isVarPropa = false; if
				 * (isReturnNode.getNodeValue().equals("true")) { isReturn =
				 * true; } else { isReturn = false;
				 * 
				 * if (dstIndexNode.getNodeValue().equals("...")) { isVarPropa =
				 * true; } }
				 * 
				 * int dstIndex = -1; if (!isVarPropa) { dstIndex = new
				 * Integer(dstIndexNode.getNodeValue()).intValue(); }
				 * 
				 * int srcIndex = new
				 * Integer(srcIndexNode.getNodeValue()).intValue(); int
				 * beginPara = new
				 * Integer(beginParaNode.getNodeValue()).intValue();
				 * 
				 * libMethod.addFeature(new
				 * LibMethodDespTdPropa(MethodFeatureType.FEATURE_TDPROPA,
				 * srcIndex, isVarPropa, dstIndex, beginPara, isReturn)); } }
				 */
				else
					if (typeNode.getNodeValue().equals("FEATRUE_RM"))
					{
						Node valueNode = node.getAttributes().getNamedItem(
								"value");
						if (valueNode != null)
						{
							libMethod.addFeature(new LibMethodDespRm(
									MethodFeatureType.FEATRUE_RM, valueNode
											.getNodeValue()));
						}
						// add by dongna
					}
			//added note by liuyan 2015.6.5
//					else
//						if (typeNode.getNodeValue().equals("FEATRUE_RR"))
//						{
//							Node valueNode = node.getAttributes().getNamedItem(
//									"value");
//							Node indexNode = node.getAttributes().getNamedItem(
//									"index");
//							int index = Integer.parseInt(indexNode
//									.getNodeValue());
//							if (valueNode != null && indexNode != null)
//							{
//								libMethod.addFeature(new LibMethodDespRR(
//										MethodFeatureType.FEATRUE_RR, valueNode
//												.getNodeValue(), index));
//							}
//						}
			//end
						else
							if (typeNode.getNodeValue().equals("RESERVED"))
							{
								libMethod.addFeature(new LibMethodDespReserved(
										MethodFeatureType.RESERVED, null));
							}
							// add by WangQian
							else
								if (typeNode.getNodeValue().equalsIgnoreCase(
										"FEATURE_MM"))
								{
									Node subType = node.getAttributes()
											.getNamedItem("subtype");
									Node paramIndex = node.getAttributes()
											.getNamedItem("paramIndex");
									if (subType != null && paramIndex != null)
									{
										String subTypeValue = subType
												.getNodeValue();
										String paramIndexValue = paramIndex
												.getNodeValue();
										LibMethodDespMM mmDesp = new LibMethodDespMM(
												MethodFeatureType.FEATURE_MM,
												subTypeValue, paramIndexValue);
										libMethod.addFeature(mmDesp);
									}
								}
								// 增加了内存分配和释放特征
								// add by zhouhb 2010/10/19
								else
									if (typeNode.getNodeValue().equals("ALLOC"))
									{

									}
									else
										if (typeNode.getNodeValue().equals(
												"FREE"))
										{

										}
			// else if (typeNode.getNodeValue().equals("ALLOCATE")) {
			// libMethod.addFeature(new
			// LibMethodDespAllocate(MethodFeatureType.ALLOCATE, null));
			// }
			/*
			 * else if (typeNode.getNodeValue().equals("API_ABUSE")) { Node
			 * descNode = node.getAttributes().getNamedItem("Description"); Node
			 * rankNode = node.getAttributes().getNamedItem("Rank");
			 * 
			 * if (descNode != null && rankNode != null) {
			 * libMethod.addFeature(new
			 * LibMethodDespAPIAbuse(MethodFeatureType.API_ABUSE,
			 * descNode.getNodeValue(), rankNode.getNodeValue())); } }else if
			 * (typeNode.getNodeValue().equals("UNCK_RET_VALUE")) { Node
			 * descNode = node.getAttributes().getNamedItem("Description"); Node
			 * rankNode = node.getAttributes().getNamedItem("Rank");
			 * 
			 * if (descNode != null && rankNode != null) {
			 * libMethod.addFeature(new
			 * LibMethodDespUnCKRetValue(MethodFeatureType.UNCK_RET_VALUE,
			 * descNode.getNodeValue(), rankNode.getNodeValue())); } }else if
			 * (typeNode.getNodeValue().equals("RR")) { Node descNode =
			 * node.getAttributes().getNamedItem("Description"); Node rankNode =
			 * node.getAttributes().getNamedItem("Rank"); Node NumNode =
			 * node.getAttributes().getNamedItem("num"); Node indexNode =
			 * node.getAttributes().getNamedItem("index");
			 * 
			 * if (descNode != null && rankNode != null && NumNode != null &&
			 * indexNode != null) { int index =
			 * Integer.parseInt(indexNode.getNodeValue()); int num =
			 * Integer.parseInt(NumNode.getNodeValue());
			 * 
			 * libMethod.addFeature(new
			 * LibMethodDespRequireRestriction(MethodFeatureType
			 * .REQUIRE_RESTRICTON, descNode.getNodeValue(),
			 * rankNode.getNodeValue(), index, num)); } }else if
			 * (typeNode.getNodeValue().equals("PWD")) { Node descNode =
			 * node.getAttributes().getNamedItem("Description"); Node rankNode =
			 * node.getAttributes().getNamedItem("Rank"); Node indexNode =
			 * node.getAttributes().getNamedItem("index"); Node subTypeNode =
			 * node.getAttributes().getNamedItem("subType"); Node fromNode =
			 * node.getAttributes().getNamedItem("from");
			 * 
			 * if (descNode != null && rankNode != null && indexNode != null &&
			 * subTypeNode != null && fromNode != null) { int index =
			 * Integer.parseInt(indexNode.getNodeValue());
			 * libMethod.addFeature(new
			 * LibMethodDespPwd(MethodFeatureType.REQUIRE_RESTRICTON,
			 * descNode.getNodeValue(), rankNode.getNodeValue(), index,
			 * subTypeNode.getNodeValue(), fromNode.getNodeValue())); } } else
			 * if (typeNode.getNodeValue().equals("BSTR")) { Node descNode =
			 * node.getAttributes().getNamedItem("Description"); Node rankNode =
			 * node.getAttributes().getNamedItem("Rank"); Node varTypeNode =
			 * node.getAttributes().getNamedItem("varType"); Node indexNode =
			 * node.getAttributes().getNamedItem("index");
			 * 
			 * if (descNode != null && rankNode != null && varTypeNode != null
			 * && indexNode != null) { int index =
			 * Integer.parseInt(indexNode.getNodeValue());
			 * 
			 * libMethod.addFeature(new
			 * LibMethodDespBSTR(MethodFeatureType.BSTR,
			 * descNode.getNodeValue(), rankNode.getNodeValue(), index,
			 * varTypeNode.getNodeValue())); } }
			 */
		}
	}

	/**
	 * 加载库函数返回值区间
	 * 
	 * @param type
	 * @param value
	 * @return
	 */
	public static Domain loadDomain(String type, String value)
	{
		if (type.equals("Point"))
		{
			return PointerDomain.valueOf(value);
		}
		else
			if (type.equals("Int"))
			{
				return IntegerDomain.valueOf(value);
			}
			else
				if (type.equals("Double"))
				{
					return DoubleDomain.valueOf(value);
				}
		return null;
	}

	public static boolean loadIsAllocate(String value)
	{
		boolean isAllocate = false;
		if (value.equals("true"))
		{
			isAllocate = true;
			return isAllocate;
		}
		else
			return isAllocate;
	}

	public static void main(String[] args)
	{
		Set<LibMethodSummary> libs = loadLibSummarys("gcc_lib//lib_summary.xml");
		for (LibMethodSummary summary : libs)
		{
			System.err.println(summary);
		}
	}
}
