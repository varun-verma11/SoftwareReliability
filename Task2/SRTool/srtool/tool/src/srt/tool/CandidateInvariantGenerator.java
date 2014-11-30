package srt.tool;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import srt.ast.BinaryExpr;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Invariant;
import srt.ast.Program;
import srt.ast.visitor.impl.DefaultVisitor;

public class CandidateInvariantGenerator {

	public List<Invariant> generateInvariants(Program p) {
		VariablesCollector vc = new VariablesCollector();
		vc.visit(p);
		List<String> vars = Arrays.asList(vc.getVariables().toArray(
				new String[0]));
		List<Invariant> invariants = new ArrayList<Invariant>();

		// Add invariants for all possible comparisons for every pair of
		// variables
		for (int i = 0; i < vars.size(); i++) {
			String v1 = vars.get(i);
			for (int j = 0; j < i; j++) {
				String v2 = vars.get(j);
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

		System.out.println("Generated " + invariants.size() + " invariants");
		return invariants;
	}

	public Program run(Program p) {
		return (Program) new CandidateInvariantInsertVisitor(
				generateInvariants(p)).visit(p);
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
