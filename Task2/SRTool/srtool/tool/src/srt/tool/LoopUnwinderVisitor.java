package srt.tool;

import java.util.ArrayList;
import java.util.List;

import srt.ast.AssertStmt;
import srt.ast.AssumeStmt;
import srt.ast.BlockStmt;
import srt.ast.EmptyStmt;
import srt.ast.IfStmt;
import srt.ast.IntLiteral;
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
		return unwindLoop(whileStmt,
				whileStmt.getBound() == null ? defaultUnwindBound : whileStmt
						.getBound().getValue());
	}

	private Stmt unwindLoop(WhileStmt whileStmt, int unwindBound) {
		if (unwindBound == 0) {
			List<Stmt> stmts = new ArrayList<Stmt>();
			if (unsound) {
				stmts.add(new AssertStmt(new IntLiteral(0)));
			}
			stmts.add(new AssumeStmt(new IntLiteral(0)));
			return new IfStmt(whileStmt.getCondition(), new BlockStmt(stmts),
					new EmptyStmt());
		}
		return new IfStmt(whileStmt.getCondition(), new BlockStmt(new Stmt[] {
				whileStmt.getBody(), unwindLoop(whileStmt, unwindBound - 1) }),
				new EmptyStmt());
	}
}
