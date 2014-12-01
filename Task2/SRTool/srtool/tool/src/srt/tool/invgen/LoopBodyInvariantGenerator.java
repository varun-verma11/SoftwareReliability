package srt.tool.invgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.Set;

import srt.ast.AssignStmt;
import srt.ast.BinaryExpr;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.Invariant;
import srt.ast.WhileStmt;

public class LoopBodyInvariantGenerator {

	public static List<Invariant> generateInvariants(WhileStmt whileStmt) {
		List<Invariant> invs = new ArrayList<Invariant>();

		// Extract conditions on variables from the loop condition.
		LoopConditionCollector c1 = new LoopConditionCollector();
		Map<String, List<BinaryExpr>> loopConditions = c1
				.extractLoopConditions(whileStmt);

		// Collect all the assignments in the while statement's body.
		LoopBodyAssignmentsCollector c2 = new LoopBodyAssignmentsCollector(
				whileStmt);
		c2.visit(whileStmt);
		Map<String, List<AssignStmt>> loopBodyAssignments = c2.getAssignments();

		Map<String, Set<Integer>> intsOccurringInAssignments = new HashMap<String, Set<Integer>>();
		for (String varName : loopBodyAssignments.keySet()) {
			Set<Integer> intLiterals = new HashSet<Integer>();
			for (AssignStmt assignStmt : loopBodyAssignments.get(varName)) {
				IntLiteralExtractorVisitor intLitVis = new IntLiteralExtractorVisitor();
				intLitVis.visit(assignStmt);
				intLiterals.addAll(intLitVis.getInts());
			}
			intsOccurringInAssignments.put(varName, intLiterals);
		}

		System.out.println("***\n\n");
		for (String varName : intsOccurringInAssignments.keySet()) {
			System.out.print("Ints occurring in assignments to " + varName
					+ ": ");
			for (Integer i : intsOccurringInAssignments.get(varName)) {
				System.out.print(i + " ");
			}
			System.out.println();
		}
		System.out.println("\n\n***");

		return invs;
	}

	// Returns the part of the binary expression which is not a sole
	// DeclRef node containing 'varName'.
	private static Expr getNonVariablePart(BinaryExpr expr, String varName) {
		if ((expr.getLhs() instanceof DeclRef)) {
			DeclRef declRef = (DeclRef) expr.getLhs();
			if (declRef.getName().equals(varName)) {
				return expr.getRhs();
			}
		}
		return expr.getLhs();
	}
}
