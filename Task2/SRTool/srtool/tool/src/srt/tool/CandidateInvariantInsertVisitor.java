package srt.tool;

import java.util.List;

import srt.ast.Invariant;
import srt.ast.InvariantList;
import srt.ast.Stmt;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class CandidateInvariantInsertVisitor extends DefaultVisitor {

	private List<Invariant> invariants;

	public CandidateInvariantInsertVisitor(List<Invariant> invariants) {
		super(true);
		this.invariants = invariants;

	}

	@Override
	public Object visit(WhileStmt stmt) {
		List<Invariant> invList = stmt.getInvariantList().getInvariants();
		invList.addAll(invariants);
		Stmt body = (Stmt) visit(stmt.getBody());
		return new WhileStmt(stmt.getCondition(), stmt.getBound(),
				new InvariantList(invList), body);
	}
}