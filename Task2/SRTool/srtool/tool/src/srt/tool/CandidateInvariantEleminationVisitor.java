package srt.tool;

import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class CandidateInvariantEleminationVisitor extends DefaultVisitor {

	public CandidateInvariantEleminationVisitor() {
		super(true);
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		//
		visit(whileStmt.getBody());
		return whileStmt;
	}
}
