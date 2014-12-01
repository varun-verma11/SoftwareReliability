package srt.tool.invgen;

import java.util.ArrayList;
import java.util.List;

import srt.ast.BinaryExpr;
import srt.ast.Invariant;
import srt.ast.WhileStmt;

public class LoopConditionInvariantGenerator {

	public static List<Invariant> generateLoopConditionInvariants(
			WhileStmt whileStmt) {
		List<Invariant> invs = new ArrayList<Invariant>();
		LoopConditionCollector c = new LoopConditionCollector(whileStmt);
		c.extractLoopConditions();
		List<BinaryExpr> conditions = c.getLoopConditionsAsList();
		for (BinaryExpr binaryExpr : conditions) {
			invs.addAll(ArithmeticInvariantGenerator
					.generateComparisonInvariants(binaryExpr.getLhs(),
							binaryExpr.getRhs()));
		}
		return invs;

	}

}
