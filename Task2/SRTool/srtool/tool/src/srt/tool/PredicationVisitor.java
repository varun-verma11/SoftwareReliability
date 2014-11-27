package srt.tool;

import java.util.ArrayList;
import java.util.List;

import srt.ast.AssertStmt;
import srt.ast.AssignStmt;
import srt.ast.AssumeStmt;
import srt.ast.BinaryExpr;
import srt.ast.BlockStmt;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.HavocStmt;
import srt.ast.IfStmt;
import srt.ast.Stmt;
import srt.ast.TernaryExpr;
import srt.ast.UnaryExpr;
import srt.ast.visitor.impl.DefaultVisitor;

public class PredicationVisitor extends DefaultVisitor {

	private int predicateCounter;
	private int havocCounter;
	private DeclRef globalPredicate;
	private DeclRef parentPredicate;

	public PredicationVisitor() {
		super(true);
		predicateCounter = 0;
		havocCounter = 0;
		parentPredicate = null;
		globalPredicate = null;
	}

	@Override
	public Object visit(IfStmt ifStmt) {
		DeclRef branchTakenPred = getFreshPredicate();
		DeclRef branchNotTakenPred = getFreshPredicate();
		Expr e = ifStmt.getCondition();
		List<Stmt> stmts = new ArrayList<Stmt>();
		stmts.add(new AssignStmt(branchTakenPred, nullSafeAnd(parentPredicate,
				e)));
		stmts.add(new AssignStmt(branchNotTakenPred, nullSafeAnd(
				parentPredicate, new UnaryExpr(UnaryExpr.LNOT, e))));

		DeclRef oldParent = parentPredicate;
		parentPredicate = branchTakenPred;
		stmts.add((Stmt) visit(ifStmt.getThenStmt()));
		parentPredicate = branchNotTakenPred;
		stmts.add((Stmt) visit(ifStmt.getElseStmt()));
		parentPredicate = oldParent;

		return new BlockStmt(stmts);
	}

	@Override
	public Object visit(AssertStmt assertStmt) {
		if (globalPredicate == null && parentPredicate == null) {
			return assertStmt;
		} else {
			return new AssertStmt(new BinaryExpr(BinaryExpr.LOR, new UnaryExpr(
					UnaryExpr.LNOT, nullSafeAnd(globalPredicate,
							parentPredicate)), assertStmt.getCondition()));
		}
	}

	@Override
	public Object visit(AssignStmt assignment) {
		if (globalPredicate == null && parentPredicate == null) {
			return assignment;
		} else {
			DeclRef variable = assignment.getLhs();
			TernaryExpr tExpr = new TernaryExpr(nullSafeAnd(globalPredicate,
					parentPredicate), assignment.getRhs(), variable);
			return new AssignStmt(variable, tExpr);
		}
	}

	@Override
	public Object visit(AssumeStmt assumeStmt) {
		if (globalPredicate != null) {
			return new AssignStmt(globalPredicate, new BinaryExpr(
					BinaryExpr.LAND, globalPredicate,
					assumeHelper(assumeStmt.getCondition())));
		} else {
			globalPredicate = new DeclRef("$G");
			return new AssignStmt(globalPredicate,
					assumeHelper(assumeStmt.getCondition()));
		}
	}

	private Expr assumeHelper(Expr expr) {
		if (parentPredicate == null) {
			return expr;
		} else {
			return new BinaryExpr(BinaryExpr.LOR, new UnaryExpr(UnaryExpr.LNOT,
					parentPredicate), expr);
		}
	}

	@Override
	public Object visit(HavocStmt havocStmt) {
		if (globalPredicate == null && parentPredicate == null) {
			return new AssignStmt(havocStmt.getVariable(), getFreshHavoc());
		} else {
			DeclRef variable = havocStmt.getVariable();
			TernaryExpr tExpr = new TernaryExpr(nullSafeAnd(globalPredicate,
					parentPredicate), getFreshHavoc(), variable,
					havocStmt.getNodeInfo());
			return new AssignStmt(variable, tExpr);
		}
	}

	private DeclRef getFreshPredicate() {
		return new DeclRef("$P" + predicateCounter++);
	}

	private DeclRef getFreshHavoc() {
		return new DeclRef("$h" + havocCounter++);
	}

	private Expr nullSafeAnd(Expr lhs, Expr rhs) {
		if (lhs == null) {
			return rhs;
		} else if (rhs == null) {
			return lhs;
		} else {
			return new BinaryExpr(BinaryExpr.LAND, lhs, rhs);
		}
	}
}