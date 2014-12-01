package srt.tool.invgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import srt.ast.BinaryExpr;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

/** Collects binary subexpressions from a loop's condition. */
public class LoopConditionCollector {

	private Map<String, List<BinaryExpr>> loopConditions;
	private WhileStmt whileStmt;

	public LoopConditionCollector(WhileStmt whileStmt) {
		loopConditions = new HashMap<String, List<BinaryExpr>>();
		this.whileStmt = whileStmt;
	}

	public void extractLoopConditions() {
		LoopConditionCollectorVisitor v = new LoopConditionCollectorVisitor();
		v.visit(whileStmt.getCondition());
		loopConditions = v.getLoopConditions();
	}

	public Map<String, List<BinaryExpr>> getLoopConditions() {
		return loopConditions;
	}

	public List<BinaryExpr> getLoopConditionsAsList() {
		List<BinaryExpr> allBinaryExprs = new ArrayList<BinaryExpr>();
		for (String varName : loopConditions.keySet()) {
			allBinaryExprs.addAll(loopConditions.get(varName));
		}
		return allBinaryExprs;
	}

	/**
	 * This visitor visits a loop's termination condition and collects binary
	 * expressions involving variables. It returns a map from variable names to
	 * binary expressions, representing termination conditions associated with
	 * each variable.
	 * 
	 * For instance, for the following loop head:
	 * <p>
	 * {@code while (i < 5 && j > (i + 5))}
	 * </p>
	 * 
	 * The visitor would return a map with two elements: {@code (i -> (i < 5))}
	 * and {@code (j -> (j > (i + 5))}.
	 */
	private class LoopConditionCollectorVisitor extends DefaultVisitor {

		private Map<String, List<BinaryExpr>> loopConditions;

		public Map<String, List<BinaryExpr>> getLoopConditions() {
			return loopConditions;
		}

		public LoopConditionCollectorVisitor() {
			super(false);
			loopConditions = new HashMap<String, List<BinaryExpr>>();
		}

		@Override
		public Object visit(BinaryExpr binaryExpr) {
			checkForConditions(binaryExpr);
			return super.visit(binaryExpr);
		}

		private void checkForConditions(BinaryExpr binaryExpr) {
			String variableName = getVariableName(binaryExpr.getLhs());
			switch (binaryExpr.getOperator()) {
			case BinaryExpr.EQUAL:
			case BinaryExpr.GEQ:
			case BinaryExpr.GT:
			case BinaryExpr.LEQ:
			case BinaryExpr.LT:
			case BinaryExpr.NEQUAL:
				if (variableName != null) {
					addLoopCondition(variableName, binaryExpr);
				} else {
					variableName = getVariableName(binaryExpr.getRhs());
					if (variableName != null) {
						addLoopCondition(variableName, binaryExpr);
					}
				}
				return;
			default:
				return;
			}
		}

		/** Adds a binary expression to the map. */
		private void addLoopCondition(String variableName, BinaryExpr binaryExpr) {
			if (loopConditions.containsKey(variableName)) {
				loopConditions.get(variableName).add(binaryExpr);
			} else {
				List<BinaryExpr> conditions = new ArrayList<BinaryExpr>();
				conditions.add(binaryExpr);
				loopConditions.put(variableName, conditions);
			}
		}

		/**
		 * Examines the given expression, returning varName if the expression is
		 * a DeclRef with name varName, or null otherwise.
		 */
		private String getVariableName(Expr expr) {
			if (!(expr instanceof DeclRef)) {
				return null;
			}
			DeclRef var = (DeclRef) expr;
			return var.getName();
		}
	}

}
