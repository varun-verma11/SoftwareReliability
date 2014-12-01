package srt.tool.invgen;

import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.visitor.impl.DefaultVisitor;

// Replaces all occurrences of varName with expr.
public class ExpressionSubstitutionVisitor extends DefaultVisitor {

	private Expr expr;
	private String varName;

	public ExpressionSubstitutionVisitor() {
		super(false);
	}

	@Override
	public Object visit(DeclRef declRef) {
		if (declRef.getName().equals(varName)) {
			return expr;
		}
		return declRef;
	}

}
