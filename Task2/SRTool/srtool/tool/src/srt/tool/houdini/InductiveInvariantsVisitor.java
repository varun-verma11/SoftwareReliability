package srt.tool.houdini;

import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;
import srt.tool.LoopAbstractionVisitor;

public class InductiveInvariantsVisitor extends DefaultVisitor {

	private LoopAbstractionVisitor visitor;

	public InductiveInvariantsVisitor(LoopAbstractionVisitor visitor) {
		super(true);
		this.visitor = visitor;
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		/*
		 * for (Invariant i :
		 * whileStmt.getCandidateInvariants().getInvariants()) { List<Stmt>
		 * blockStmtList = new ArrayList<Stmt>(); blockStmtList.add(new
		 * AssumeStmt(i.getExpr())); blockStmtList.add(new
		 * IfStmt(whileStmt.getCondition(), new BlockStmt(new Stmt[] {
		 * whileStmt.getBody(), new AssertStmt(i.getExpr()) }), new
		 * EmptyStmt())); BlockStmt block = new BlockStmt(blockStmtList);
		 * CollectConstraintsVisitor constraintsVisitor = new
		 * CollectConstraintsVisitor(); constraintsVisitor.visit(block); }
		 * return null;
		 */
		return null;
	}
}
