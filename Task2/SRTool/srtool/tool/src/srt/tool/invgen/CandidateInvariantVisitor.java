package srt.tool.invgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import srt.ast.AssignStmt;
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
		ArithmeticExpressionExtractor v = new ArithmeticExpressionExtractor();
		List<Invariant> invs = new ArrayList<Invariant>();

		invs.addAll(whileStmt.getInvariantList().getInvariants());
		invs.addAll(v.generateArithmeticCandidates(whileStmt));
		invs.addAll(mostRecentAssignmentInvariants(whileStmt));

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
			System.out.println("Testing for variable " + variableName
					+ " \n\n\n");
			if (mostRecentAssignments.containsKey(variableName)) {
				System.out.println("Containzzz\n\n\n\n");
				mostRecentAssignmentInvariants
						.addAll(ArithmeticInvariantGenerator
								.generateAssignmentInvariants(variableName,
										mostRecentAssignments.get(variableName)));
			}
		}
		return mostRecentAssignmentInvariants;
	}
}
