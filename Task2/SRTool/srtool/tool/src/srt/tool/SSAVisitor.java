package srt.tool;

import java.util.HashMap;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.visitor.impl.DefaultVisitor;

public class SSAVisitor extends DefaultVisitor {
	private Map<String, Integer> variableCount = new HashMap<String, Integer>();

	public SSAVisitor() {
		super(true);
	}

	/**
	 * Initialise count for new variable declared
	 */
	@Override
	public Object visit(Decl decl) {
		String varName = decl.getName();
		variableCount.put(varName, 0);
		return new Decl(getNameWithIndex(varName), decl.getType(),
				decl.getNodeInfo());
	}

	/**
	 * Add the incremented variable count to the variable name and then return a
	 * new DeclRef node
	 */
	@Override
	public Object visit(DeclRef declRef) {
		String name = declRef.getName();
		return new DeclRef(getNameWithIndex(name), declRef.getNodeInfo());
	}

	@Override
	public Object visit(AssignStmt assignment) {
		Expr rhs = (Expr) this.visit(assignment.getRhs());
		incrementVariableCount(assignment.getLhs().getName());
		DeclRef lhs = (DeclRef) this.visit(assignment.getLhs());
		return new AssignStmt(lhs, rhs);
	}

	private String getNameWithIndex(String name) {
		return name + '$' + variableCount.get(name);
	}

	private void incrementVariableCount(String name) {
		variableCount.put(name, variableCount.get(name) + 1);
	}

}
