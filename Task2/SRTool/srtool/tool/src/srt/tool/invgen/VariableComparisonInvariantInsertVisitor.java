package srt.tool.invgen;

import java.util.List;

import srt.ast.Invariant;
import srt.ast.InvariantList;
import srt.ast.Stmt;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class VariableComparisonInvariantInsertVisitor extends DefaultVisitor {

	private List<Invariant> invariants;

	public VariableComparisonInvariantInsertVisitor(List<Invariant> invariants) {
		super(true);
		this.invariants = invariants;
	}

	@Override
	public Object visit(WhileStmt stmt) {
		List<Invariant> invList = stmt.getInvariantList().getInvariants();
		for (Invariant i : invariants) {
			invList.add(new Invariant(true, i.getExpr()));
		}
		Stmt body = (Stmt) visit(stmt.getBody());
		return new WhileStmt(stmt.getCondition(), stmt.getBound(),
				new InvariantList(invList), body);
	}
}