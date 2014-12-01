package srt.tool.invgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.Invariant;
import srt.ast.InvariantList;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;
import srt.util.StmtUtil;

public class CandidateInvariantVisitor extends DefaultVisitor {

	private Map<String, Expr> mostRecentAssignments;

	public CandidateInvariantVisitor() {
		super(true);
		mostRecentAssignments = new HashMap<String, Expr>();
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		List<Invariant> invs = new ArrayList<Invariant>();

		// Keep all of the existing invariants.
		invs.addAll(whileStmt.getInvariantList().getInvariants());

		// Generate invariants based solely on the expressions in the loop's
		// condition.
		invs.addAll(LoopConditionInvariantGenerator
				.generateLoopConditionInvariants(whileStmt));

		// Generate invariants based on the expressions in the loop's condition
		// and assignments encountered in the loop body.
		invs.addAll(LoopBodyAssignmentsInvariantGenerator
				.generateInvariants(whileStmt));

		// Generate invariants based on most recent assignments into variables
		// in the loop's modset.
		invs.addAll(mostRecentAssignmentInvariants(whileStmt));

		// Recursively visit children.
		WhileStmt visitedResult = (WhileStmt) super.visit(whileStmt);

		return new WhileStmt(whileStmt.getCondition(), whileStmt.getBound(),
				new InvariantList(invs), visitedResult.getBody());
	}

	@Override
	public Object visit(AssignStmt assignStmt) {
		mostRecentAssignments.put(assignStmt.getLhs().getName(),
				assignStmt.getRhs());
		return super.visit(assignStmt);
	}

	private List<Invariant> mostRecentAssignmentInvariants(WhileStmt whileStmt) {
		List<Invariant> mostRecentAssignmentInvariants = new ArrayList<Invariant>();
		for (String variableName : StmtUtil.computeModSet(whileStmt)) {
			if (mostRecentAssignments.containsKey(variableName)) {
				mostRecentAssignmentInvariants
						.addAll(ArithmeticInvariantGenerator
								.generateComparisonInvariants(new DeclRef(
										variableName), mostRecentAssignments
										.get(variableName)));
			}
		}
		return mostRecentAssignmentInvariants;
	}
}
