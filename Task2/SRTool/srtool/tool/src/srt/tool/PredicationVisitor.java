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
	private final DeclRef globalPredicate;
	private DeclRef parentPredicate;

	public PredicationVisitor() {
		super(true);
		predicateCounter = 0;
		havocCounter = 0;
		globalPredicate = new DeclRef("$G");
		parentPredicate = globalPredicate;
	}

	@Override
	public Object visit(IfStmt ifStmt) {
		DeclRef branchTakenPred = getFreshPredicate();
		DeclRef branchNotTakenPred = getFreshPredicate();
		Expr e = ifStmt.getCondition();
		List<Stmt> stmts = new ArrayList<Stmt>();
		stmts.add(new AssignStmt(branchTakenPred, new BinaryExpr(
				BinaryExpr.LAND, parentPredicate, e)));
		stmts.add(new AssignStmt(branchNotTakenPred, new BinaryExpr(
				BinaryExpr.LAND, parentPredicate, new UnaryExpr(UnaryExpr.LNOT,
						e))));
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
		return new AssertStmt(new BinaryExpr(//
				BinaryExpr.LOR,//
				new UnaryExpr(UnaryExpr.LNOT,//
						new BinaryExpr(BinaryExpr.LAND,//
								globalPredicate, parentPredicate)),//
				assertStmt.getCondition()));
	}

	@Override
	public Object visit(AssignStmt assignment) {
		DeclRef variable = assignment.getLhs();
		TernaryExpr tExpr = new TernaryExpr(//
				new BinaryExpr(BinaryExpr.LAND, globalPredicate,
						parentPredicate),//
				assignment.getRhs(), variable);
		return new AssignStmt(variable, tExpr);
	}

	@Override
	public Object visit(AssumeStmt assumeStmt) {
		return new AssignStmt(globalPredicate, new BinaryExpr(BinaryExpr.LAND,
				globalPredicate,//
				new BinaryExpr(//
						BinaryExpr.LOR,//
						new UnaryExpr(UnaryExpr.LNOT, globalPredicate),//
						assumeStmt.getCondition())));
	}

	@Override
	public Object visit(HavocStmt havocStmt) {
		DeclRef variable = havocStmt.getVariable();
		TernaryExpr tExpr = new TernaryExpr(//
				new BinaryExpr(BinaryExpr.LAND, globalPredicate,
						parentPredicate),//
				getFreshHavoc(), variable, havocStmt.getNodeInfo());
		return new AssignStmt(variable, tExpr);
	}

	private DeclRef getFreshPredicate() {
		return new DeclRef("$P" + predicateCounter++);
	}

	private DeclRef getFreshHavoc() {
		return new DeclRef("$h" + havocCounter++);
	}
}