package srt.tool.invgen;

import java.util.HashSet;
import java.util.Set;

import srt.ast.AssignStmt;
import srt.ast.DeclRef;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;

public class VariableNameCollector extends DefaultVisitor {
	private Set<String> variables = new HashSet<String>();
	private int loopCount = 0;

	public VariableNameCollector() {
		super(false);
	}

	@Override
	public Object visit(AssignStmt stmt) {
		if (loopCount > 0)
			variables.add(stmt.getLhs().getName());
		return stmt;
	}

	@Override
	public Object visit(WhileStmt stmt) {
		loopCount++;
		Object o = super.visit(stmt);
		loopCount--;
		return o;
	}

	@Override
	public Object visit(DeclRef stmt) {
		variables.add(stmt.getName());
		return stmt;
	}

	public Set<String> getVariables() {
		return variables;
	}
}