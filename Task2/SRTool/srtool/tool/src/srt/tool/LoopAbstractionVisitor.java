package srt.tool;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import srt.ast.AssertStmt;
import srt.ast.AssignStmt;
import srt.ast.AssumeStmt;
import srt.ast.BlockStmt;
import srt.ast.DeclRef;
import srt.ast.EmptyStmt;
import srt.ast.HavocStmt;
import srt.ast.IfStmt;
import srt.ast.IntLiteral;
import srt.ast.Invariant;
import srt.ast.Node;
import srt.ast.Stmt;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class LoopAbstractionVisitor extends DefaultVisitor {

	public LoopAbstractionVisitor() {
		super(true);
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		List<Stmt> blockStmts = new ArrayList<Stmt>();
		List<Invariant> trueInvariants = whileStmt.getTrueInvariants()
				.getInvariants();

		blockStmts.addAll(assertInvariants(trueInvariants));
		blockStmts.addAll(havocModset(whileStmt));
		blockStmts.addAll(assumeInvariants(trueInvariants));

		List<Stmt> ifStatementBlockStmts = new ArrayList<Stmt>();
		// To handle nested loops, we first visit the body of the loop and then
		// add it to the body of the resulted if statement.
		ifStatementBlockStmts.add((Stmt) visit(whileStmt.getBody()));
		ifStatementBlockStmts.addAll(assertInvariants(trueInvariants));
		ifStatementBlockStmts.add(new AssumeStmt(new IntLiteral(0)));

		blockStmts.add(new IfStmt(whileStmt.getCondition(), new BlockStmt(
				ifStatementBlockStmts), new EmptyStmt()));

		return new BlockStmt(blockStmts);
	}

	private Set<DeclRef> computeModSet(Node node) {
		Set<DeclRef> modset = new HashSet<DeclRef>();
		if (node == null) {
			return modset;
		}
		if (node instanceof AssignStmt) {
			modset.add(((AssignStmt) node).getLhs());
		} else {
			for (Node child : node.getChildrenCopy()) {
				modset.addAll(computeModSet(child));
			}
		}
		return modset;
	}

	private List<Stmt> havocModset(WhileStmt stmt) {
		List<Stmt> havocStmts = new ArrayList<Stmt>();
		for (DeclRef declRef : computeModSet(stmt.getBody())) {
			havocStmts.add(new HavocStmt(declRef));
		}
		return havocStmts;
	}

	private List<Stmt> assumeInvariants(List<Invariant> invs) {
		List<Stmt> invariantAssumeStmts = new ArrayList<Stmt>();
		for (Invariant i : invs) {
			invariantAssumeStmts.add(new AssumeStmt(i.getExpr()));
		}
		return invariantAssumeStmts;
	}

	private List<Stmt> assertInvariants(List<Invariant> invs) {
		List<Stmt> invariantAssertStmts = new ArrayList<Stmt>();
		for (Invariant i : invs) {
			invariantAssertStmts.add(new AssertStmt(i.getExpr()));
		}
		return invariantAssertStmts;
	}
}