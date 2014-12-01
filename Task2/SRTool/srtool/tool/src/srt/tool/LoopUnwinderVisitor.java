package srt.tool;

import java.util.ArrayList;
import java.util.List;

import srt.ast.AssertStmt;
import srt.ast.AssumeStmt;
import srt.ast.BlockStmt;
import srt.ast.EmptyStmt;
import srt.ast.IfStmt;
import srt.ast.IntLiteral;
import srt.ast.Invariant;
import srt.ast.Stmt;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class LoopUnwinderVisitor extends DefaultVisitor {

	private boolean unsound;
	private int defaultUnwindBound;

	public LoopUnwinderVisitor(boolean unsound, int defaultUnwindBound) {
		super(true);
		this.unsound = unsound;
		this.defaultUnwindBound = defaultUnwindBound;
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		List<Stmt> invariantAssertions = new ArrayList<Stmt>();

		for (Invariant i : whileStmt.getInvariantList().getInvariants()) {
			if (!i.isCandidate()) {
				invariantAssertions.add(new AssertStmt(i.getExpr()));
			}
		}
		Stmt result = (Stmt) visit(whileStmt.getBody());
		WhileStmt newStmt = new WhileStmt(whileStmt.getCondition(),
				whileStmt.getBound(), whileStmt.getInvariantList(), result);
		return unwindLoop(newStmt,
				newStmt.getBound() == null ? defaultUnwindBound : newStmt
						.getBound().getValue(), invariantAssertions);
	}

	private Stmt unwindLoop(WhileStmt whileStmt, int unwindBound,
			List<Stmt> invariantAssertions) {
		List<Stmt> unwindBlockStmts = new ArrayList<Stmt>();
		IfStmt ifStmt;
		if (unwindBound == 0) {
			List<Stmt> ifBlockStmts = new ArrayList<Stmt>();
			if (!unsound) {
				ifBlockStmts.add(new AssertStmt(new IntLiteral(0)));
			}
			ifBlockStmts.add(new AssumeStmt(new IntLiteral(0)));
			ifStmt = new IfStmt(whileStmt.getCondition(), new BlockStmt(
					ifBlockStmts), new EmptyStmt());
		} else {
			ifStmt = new IfStmt(whileStmt.getCondition(), new BlockStmt(
					new Stmt[] {
							whileStmt.getBody(),
							unwindLoop(whileStmt, unwindBound - 1,
									invariantAssertions) }), new EmptyStmt());
		}
		unwindBlockStmts.addAll(invariantAssertions);
		unwindBlockStmts.add(ifStmt);
		return new BlockStmt(unwindBlockStmts);
	}
}
