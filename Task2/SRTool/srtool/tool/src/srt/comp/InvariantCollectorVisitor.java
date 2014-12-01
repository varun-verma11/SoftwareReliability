package srt.comp;

import java.util.ArrayList;
import java.util.List;

import srt.ast.Invariant;
import srt.ast.Node;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

/**
 * @author Varun Verma
 * 
 */
public class InvariantCollectorVisitor extends DefaultVisitor {

	private List<Invariant> invariants = new ArrayList<Invariant>();

	public InvariantCollectorVisitor() {
		super(false);
	}

	@Override
	public Object visit(WhileStmt stmt) {
		invariants.addAll(stmt.getInvariantList().getInvariants());
		return super.visit(stmt);
	}

	private List<Invariant> getInvariants() {
		return invariants;
	}

	public static List<Invariant> run(Node p) {
		InvariantCollectorVisitor invariantCollectorVisitor = new InvariantCollectorVisitor();
		invariantCollectorVisitor.visit(p);
		return invariantCollectorVisitor.getInvariants();
	}
}
