package srt.tool;

import java.util.HashMap;
import java.util.Map;

import srt.ast.AssignStmt;
import srt.ast.Decl;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.visitor.impl.DefaultVisitor;

public class SSAVisitor extends DefaultVisitor {
	/** A map for remembering the SSA renaming count for each variable. */
	private Map<String, Integer> variableCount = new HashMap<String, Integer>();

	public SSAVisitor() {
		super(true);
	}

	/** Places each declared variable in the map, with initial count 0. */
	@Override
	public Object visit(Decl decl) {
		String varName = decl.getName();
		variableCount.put(varName, 0);
		return new Decl(getNameWithIndex(varName), decl.getType(),
				decl.getNodeInfo());
	}

	/** Performs the SSA renaming. */
	@Override
	public Object visit(DeclRef declRef) {
		return new DeclRef(getNameWithIndex(declRef.getName()),
				declRef.getNodeInfo());
	}

	/** Increases a variable's renaming index after an assignment into it. */
	@Override
	public Object visit(AssignStmt assignment) {
		Expr rhs = (Expr) this.visit(assignment.getRhs());
		incrementVariableCount(assignment.getLhs().getName());
		return new AssignStmt((DeclRef) this.visit(assignment.getLhs()), rhs);
	}

	private String getNameWithIndex(String name) {
		return name + '$' + variableCount.get(name);
	}

	private void incrementVariableCount(String name) {
		variableCount.put(name,
				variableCount.containsKey(name) ? variableCount.get(name) + 1
						: 0);
	}
}
