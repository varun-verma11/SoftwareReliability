package srt.ast;

public class AssertStmt extends Stmt {
	
	public AssertStmt(Expr condition) {
		this(condition, null);
	}
	
	public AssertStmt(Expr condition, NodeInfo nodeInfo) {
		super(nodeInfo);
		children.add(condition);
	}
	
	public Expr getCondition() {
		return (Expr) children.get(0);
	}
}
