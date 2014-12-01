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

	public Map<String, List<BinaryExpr>> extractLoopConditions(
			WhileStmt whileStmt) {
		LoopConditionCollectorVisitor v = new LoopConditionCollectorVisitor();
		v.visit(whileStmt.getCondition());
		return v.getLoopConditions();
	}

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
			if (variableName != null) {
				addLoopCondition(variableName, binaryExpr);
			} else {
				variableName = getVariableName(binaryExpr.getRhs());
				addLoopCondition(variableName, binaryExpr);
			}
		}

		private void addLoopCondition(String variableName, BinaryExpr binaryExpr) {
			if (loopConditions.containsKey(variableName)) {
				loopConditions.get(variableName).add(binaryExpr);
			} else {
				List<BinaryExpr> conditions = new ArrayList<BinaryExpr>();
				conditions.add(binaryExpr);
				loopConditions.put(variableName, conditions);
			}
		}

		private String getVariableName(Expr expr) {
			if (!(expr instanceof DeclRef)) {
				return null;
			}
			DeclRef var = (DeclRef) expr;
			return var.getName();
		}
	}

}
