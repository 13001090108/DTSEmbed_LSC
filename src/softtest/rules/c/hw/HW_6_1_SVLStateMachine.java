package softtest.rules.c.hw;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.LinkedList;
import java.util.List;
import java.util.Map;
import java.util.Set;

import org.jaxen.JaxenException;

import softtest.ast.c.ASTIterationStatement;
import softtest.ast.c.ASTPrimaryExpression;
import softtest.ast.c.Node;
import softtest.ast.c.SimpleNode;
import softtest.cfg.c.VexNode;
import softtest.fsm.c.FSMMachine;
import softtest.fsm.c.FSMMachineInstance;
import softtest.rules.c.StateMachineUtils;
import softtest.symboltable.c.NameOccurrence;
import softtest.symboltable.c.VariableNameDeclaration;
import softtest.symboltable.c.NameOccurrence.OccurrenceType;

/**
 * <p>
 * SVL - Same loop Variable used in nested Loop.<br>
 * 多重循环使用同样的循环变量.
 * </p>
 */
public class HW_6_1_SVLStateMachine {

    /**
     * <p>
     * Created SVL state machine instances for the specific function.<br>
     * It's called by reflection.
     * </p>
     * 
     * @param node
     *            the ast node of the function, it's FunctionDefinition in
     *            default, TranslationUnit when Scop="File" was used in xml
     * @param fsm
     *            the finite state machine object generated by parsing the xml
     *            fsm descriptor, it's the template of the fsm instance
     * @return the list of finite state machine instance
     */
    public static List<FSMMachineInstance> createSVLStateMachines(
            SimpleNode node, FSMMachine fsm) {
        // hold the result
        List<FSMMachineInstance> list = new LinkedList<FSMMachineInstance>();
        // find all outer loop which has at least one inner loop
        String xpath = ".//CompoundStatement/StatementList/Statement/IterationStatement[.//IterationStatement]|" +
        		".//CompoundStatement/StatementList/Statement/LabeledStatement/Statement/IterationStatement[.//IterationStatement]";
        List<SimpleNode> evaluationResults = StateMachineUtils
                .getEvaluationResults(node, xpath);
        // hold loop variable
        Map<VariableNameDeclaration, SimpleNode> loopVariables = new HashMap<VariableNameDeclaration, SimpleNode>();
        ASTIterationStatement itrNode = null;
        for (SimpleNode snode : evaluationResults) {
        	loopVariables.clear();
        	if(!snode.getParentsOfType(ASTIterationStatement.class).isEmpty()) {
        		continue;
        	}
            itrNode = (ASTIterationStatement) snode;
            do {
                Set<VariableNameDeclaration> result = findLoopVariable(
                        findLoopVariableCandidate(itrNode), itrNode);
                for (VariableNameDeclaration loopVariable : result) {
                    if (loopVariables.containsKey(loopVariable)) {
                        FSMMachineInstance fsminstance = fsm.creatInstance();
                        fsminstance.setRelatedASTNode(itrNode);
                        fsminstance.setRelatedVariable(loopVariable);
                        fsminstance.setDesp("第"
                                + loopVariables.get(loopVariable)
                                        .getBeginLine() + "行的循环和第"
                                + itrNode.getBeginLine() + "行的循环使用了相同的循环变量"
                                + loopVariable.getImage());
                        list.add(fsminstance);
                    } else {
                        loopVariables.put(loopVariable, snode);
                    }
                }
                List<Node> temp = itrNode
                        .findChildrenOfType(ASTIterationStatement.class);
                // the first one is snode itself if there exsists
                itrNode = temp.size() <= 1 ? null
                        : (ASTIterationStatement) temp.get(1);
            } while (itrNode != null);
        }
        return list;
    }

    /**
     * <p>
     * Find loop variable candidates of a iteration.<br>
     * The variable used in loop terminate condition can be a candidate.
     * </p>
     * 
     * @param itrNode
     *            the ast node of the iteration, it's ASTIterationStatement
     * @return the loop variable candidates
     */
    private static Set<VariableNameDeclaration> findLoopVariableCandidate(
            ASTIterationStatement itrNode) {
        // hold the result
        Set<VariableNameDeclaration> result = new HashSet<VariableNameDeclaration>();

        // prepare the xpath navigation for the expressions which are used as
        // loop condition
        String varXpath = "/UnaryExpression/PostfixExpression[count(*)=1]/PrimaryExpression[count(*)=0]";

        String xpathString = "/Expression//RelationalExpression" + varXpath // i>n
                + "|/Expression/AssignmentExpression" + varXpath // i
                + "|/Expression//LogicalANDExpression" + varXpath // a && i>0
                + "|/Expression//LogicalORExpression" + varXpath; // a || i>0

        String loopType = itrNode.getImage();
        if (loopType.equals("for")) {
            // for
            int n = -1;
            // find the index of the second expression, -1 means it does not
            // exsit
            if (itrNode.forChild[1]) {
                if (itrNode.forChild[0]) {
                    n = 2;
                } else {
                    n = 1;
                }
            }
            if (n == -1) {
                // no need to process further, we consider there is no loop
                // variable
                return result;
            } else {
                // change the xpath expression
                xpathString = xpathString.replaceAll("/Expression",
                        "/Expression[" + n + "]");
            }
        }
        // find candidate using xpath for three kinds of loop(while, do-while
        // and for)
        List candidateList = findChildNodesWithXPath(itrNode, xpathString);
        for (Object o : candidateList) {
            ASTPrimaryExpression varNode = (ASTPrimaryExpression) o;
            VariableNameDeclaration varDecl = varNode.getVariableDecl();
            if (varDecl != null) {
                result.add(varDecl);
            }
        }
        return result;
    }

    /**
     * <p>
     * Confirm the loop variable in candidates.<br>
     * The candidate domain which changes in the loop can be chosen.
     * </p>
     * 
     * @param candidates
     *            the loop variable candidates
     * @param itrNode
     *            the ast node of the iteration, it's ASTIterationStatement
     * @return the loop variable candidates
     */
    private static Set<VariableNameDeclaration> findLoopVariable(
            Set<VariableNameDeclaration> candidates,
            ASTIterationStatement itrNode) {
        if (candidates.size() == 1 || candidates.size() == 0) {
            // if only one candidate was found, it's the loop variable
            return candidates;
        }
        Set<VariableNameDeclaration> loopVar = new HashSet<VariableNameDeclaration>();
        // find the variable used in the statement of the loop and check if it's
        // domain changed, ### is the place holder
        String xpathString = "/Statement/CompoundStatement/StatementList/Statement/ExpressionStatement//PrimaryExpression[@Image='###']";

        // for loop should check the 3rd expression under itrNode if exists
        String forPath = null;
        if (itrNode.getImage().equals("for")) {
            forPath = "/Expression//PrimaryExpression[@Image='###']";
            if (itrNode.forChild[2]) {
                // index of 3rd expression
                int n = 3;
                if (!itrNode.forChild[0] && !itrNode.forChild[1]) {
                    n = 1;
                } else if (itrNode.forChild[0] ^ itrNode.forChild[1]) {
                    n = 2;
                }
                forPath = forPath.replace("/Expression", "/Expression[" + n
                        + "]");
            }
        }
        for (Iterator<VariableNameDeclaration> itr = candidates.iterator(); itr
                .hasNext();) {
            VariableNameDeclaration varDecl = itr.next();
            String xpath = xpathString.replace("###", varDecl.getImage());
            List varOcc = findChildNodesWithXPath(itrNode, xpath);
            if (forPath != null) {
                forPath = forPath.replace("###", varDecl.getImage());
                List temp = findChildNodesWithXPath(itrNode, forPath);
                varOcc.addAll(temp);
            }
            boolean changed = false;
            for (Object o : varOcc) {
                SimpleNode snode = (SimpleNode) o;
                VexNode vex = snode.getCurrentVexNode();
                // Domain domain = vex.getDomain(varDecl);
                // Domain lastDomain = getLastDomain(snode);
                // if (!domain.equals(lastDomain)) {
                // changed = true;
                // break;
                // }
                ArrayList<NameOccurrence> occs = vex.getOccurrences();
                for (NameOccurrence occ : occs) {
                    if (occ.getDeclaration() == varDecl) {
                        if (occ.getOccurrenceType() == OccurrenceType.DEF_AFTER_USE) {
                            changed = true;
                        }
                        break;
                    }
                }
                if (changed) {
                    break;
                }
            }
//            if (changed) {
                loopVar.add(varDecl);
//            }
        }
        return loopVar;
    }

    /**
     * <p>
     * Find child Nodes with xpath, wrap the exception and return an empty list.
     * </p>
     * 
     * @param node
     *            the ast node
     * @param xpath
     *            the String which represents a xpath expression
     * @return the List contains the result ast node
     */
    private static List findChildNodesWithXPath(SimpleNode node, String xpath) {
        try {
            return node.findChildNodesWithXPath(xpath);
        } catch (JaxenException e) {
            return new ArrayList();
        }
    }

}
