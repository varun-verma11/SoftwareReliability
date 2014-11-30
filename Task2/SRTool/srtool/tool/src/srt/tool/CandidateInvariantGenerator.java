package srt.tool;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import srt.ast.BinaryExpr;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Invariant;
import srt.ast.InvariantList;
import srt.ast.Program;
import srt.ast.Stmt;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class CandidateInvariantGenerator {

	private List<Invariant> generateInvariants(Program p) {
		VariablesCollector vc = new VariablesCollector();
		vc.visit(p);
		Set<String> vars = vc.getVariables();
		List<Invariant> invariants = new ArrayList<Invariant>();

		// Add invariants for all possible comparisons for every pair of
		// variables
		for (String v1 : vars) {
			for (String v2 : vars) {
				if (!v1.equals(v2)) {
					invariants
							.add(new Invariant(true, new BinaryExpr(
									BinaryExpr.EQUAL, new DeclRef(v1),
									new DeclRef(v2))));
					invariants.add(new Invariant(true,
							new BinaryExpr(BinaryExpr.NEQUAL, new DeclRef(v1),
									new DeclRef(v2))));
					invariants.add(new Invariant(true, new BinaryExpr(
							BinaryExpr.GT, new DeclRef(v1), new DeclRef(v2))));
					invariants.add(new Invariant(true, new BinaryExpr(
							BinaryExpr.LT, new DeclRef(v1), new DeclRef(v2))));
				}
			}
		}

		System.out.println("Generated " + invariants.size() + "invariants");
		return invariants;
	}

	public Program run(Program p) {
		return (Program) new CandidateInvariantInsertVisitor(
				generateInvariants(p)).visit(p);
	}

	private class CandidateInvariantInsertVisitor extends DefaultVisitor {

		private List<Invariant> invariants;

		public CandidateInvariantInsertVisitor(List<Invariant> invariants) {
			super(true);
			this.invariants = invariants;

		}

		@Override
		public Object visit(WhileStmt stmt) {
			// FIXME: need to check if this works since it will be referencing
			// to objects from global list so could fail in Houdini
			List<Invariant> invList = stmt.getInvariantList().getInvariants();
			invList.addAll(invariants);
			Stmt body = (Stmt) visit(stmt.getBody());
			return new WhileStmt(stmt.getCondition(), stmt.getBound(),
					new InvariantList(invList), body);
		}
	}

	private class VariablesCollector extends DefaultVisitor {

		private Set<String> variables = new HashSet<String>();

		public VariablesCollector() {
			super(false);
		}

		@Override
		public Object visit(Decl stmt) {
			variables.add(stmt.getName());
			return stmt;
		}

		@Override
		public Object visit(DeclRef stmt) {
			variables.add(stmt.getName());
			return stmt;
		}

		public Set<String> getVariables() {
			return variables;
		}
	}

}
