package srt.tool;

import srt.ast.AssertStmt;
import srt.ast.EmptyStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class AssertionRemoverVisitor extends DefaultVisitor {

	public AssertionRemoverVisitor() {
		super(true);
	}

	@Override
	public Object visit(AssertStmt assertStmt) {
		return new EmptyStmt();
	}

}
