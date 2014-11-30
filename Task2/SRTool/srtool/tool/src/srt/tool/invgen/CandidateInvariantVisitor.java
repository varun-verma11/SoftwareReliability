package srt.tool.invgen;

import java.util.ArrayList;
import java.util.List;

import srt.ast.Invariant;
import srt.ast.InvariantList;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class CandidateInvariantVisitor extends DefaultVisitor {

	public CandidateInvariantVisitor() {
		super(true);
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		ArithmeticExpressionExtractor v = new ArithmeticExpressionExtractor();
		List<Invariant> invs = new ArrayList<Invariant>();

		invs.addAll(whileStmt.getInvariantList().getInvariants());
		invs.addAll(v.generateArithmeticCandidates(whileStmt));
		System.out.println("***\n\n" + invs.size() + "\n\n****");
		WhileStmt visitedResult = (WhileStmt) super.visit(whileStmt);
		return new WhileStmt(whileStmt.getCondition(), whileStmt.getBound(),
				new InvariantList(invs), visitedResult.getBody());
	}
}
