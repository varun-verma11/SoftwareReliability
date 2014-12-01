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
import srt.ast.IntLiteral;
import srt.ast.Invariant;
import srt.ast.WhileStmt;

/**
 * Adds candidate invariants based on assignments to variables encountered in
 * the loop body. For a simple while loop
 * <p>
 * while (i < 5) { i = i + 3; }
 * <p>
 * this class will:
 * <ul>
 * <li>identify all simple comparisons on variables in the loop condition:
 * {@code i < 5}.
 * <li>identify all assignments into variables in the loop body:
 * {@code i = i + 3}
 * <li>extract all the int values encountered in these assignments and construct
 * a map from variables to lists of integers: {@code i -> [3]}
 * <li>generate invariants based on the loop conditions on each variable and the
 * int values assigned to it: {@code i < 5 + 3, i > 5 - 3, i >= 5 + 3} etc.
 * 
 * @author pc2211
 * 
 */
public class LoopBodyAssignmentsInvariantGenerator {

	public static List<Invariant> generateInvariants(WhileStmt whileStmt) {

		// Extract conditions on variables from the loop condition.
		LoopConditionCollector c1 = new LoopConditionCollector(whileStmt);
		c1.extractLoopConditions();
		Map<String, List<BinaryExpr>> loopConditions = c1.getLoopConditions();

		// Collect all the assignments in the while statement's body.
		LoopBodyAssignmentsCollector c2 = new LoopBodyAssignmentsCollector(
				whileStmt);
		c2.visit(whileStmt);
		Map<String, List<AssignStmt>> loopBodyAssignments = c2.getAssignments();

		// Collect all int values occurring in assignments to variables in the
		// loop body.
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
		return generateAssignmentInvariants(loopConditions,
				loopBodyAssignments, intsOccurringInAssignments);
	}

	private static List<Invariant> generateAssignmentInvariants(
			Map<String, List<BinaryExpr>> loopConditions,
			Map<String, List<AssignStmt>> loopBodyAssignments,
			Map<String, Set<Integer>> intsOccurringInAssignments) {
		List<Invariant> invs = new ArrayList<Invariant>();
		for (String varName : loopConditions.keySet()) {
			for (BinaryExpr bExpr : loopConditions.get(varName)) {
				Expr nonVariablePart = getNonVariablePart(bExpr, varName);
				// If the variable currently being analysed is never assigned to
				// in the loop, we can't generate any invariants of this type
				// for it. Skip to the next variable.
				if (intsOccurringInAssignments.get(varName) == null) {
					continue;
				}
				for (Integer i : intsOccurringInAssignments.get(varName)) {
					for (BinaryExpr combinedBExpr : combine(nonVariablePart, i)) {

						if (bExpr.getLhs() == nonVariablePart) {
							invs.addAll(ArithmeticInvariantGenerator
									.generateComparisonInvariants(
											combinedBExpr, bExpr.getRhs()));
						} else {
							invs.addAll(ArithmeticInvariantGenerator
									.generateComparisonInvariants(
											bExpr.getLhs(), combinedBExpr));
						}
					}
				}
			}
		}
		invs.addAll(generateIntLiteralCandidates(intsOccurringInAssignments));
		return invs;
	}

	private static List<Invariant> generateIntLiteralCandidates(
			Map<String, Set<Integer>> intsOccurringInAssignments) {
		List<Invariant> invs = new ArrayList<Invariant>();
		for (String varName : intsOccurringInAssignments.keySet()) {
			for (Integer i : intsOccurringInAssignments.get(varName)) {
				invs.addAll(generateModularInvariants(varName, i));
			}
		}
		return invs;
	}

	private static List<BinaryExpr> combine(Expr expr, int i) {
		List<BinaryExpr> invs = new ArrayList<BinaryExpr>();
		invs.add(new BinaryExpr(BinaryExpr.ADD, expr, new IntLiteral(i)));
		invs.add(new BinaryExpr(BinaryExpr.SUBTRACT, expr, new IntLiteral(i)));
		return invs;
	}

	private static List<Invariant> generateModularInvariants(String varName,
			int value) {
		List<Invariant> invs = new ArrayList<Invariant>();
		BinaryExpr varNameModValue = new BinaryExpr(BinaryExpr.MOD,
				new DeclRef(varName), new IntLiteral(value));
		invs.add(new Invariant(true, new BinaryExpr(BinaryExpr.EQUAL,
				varNameModValue, new IntLiteral(0))));
		invs.add(new Invariant(true, new BinaryExpr(BinaryExpr.NEQUAL,
				varNameModValue, new IntLiteral(0))));
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
