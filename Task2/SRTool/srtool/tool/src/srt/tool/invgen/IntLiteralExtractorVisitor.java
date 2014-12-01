package srt.tool.invgen;

import java.util.HashSet;
import java.util.Set;

import srt.ast.IntLiteral;
import srt.ast.visitor.impl.DefaultVisitor;

public class IntLiteralExtractorVisitor extends DefaultVisitor {

	private Set<Integer> ints;

	public Set<Integer> getInts() {
		return ints;
	}

	public IntLiteralExtractorVisitor() {
		super(false);
		ints = new HashSet<Integer>();
	}

	@Override
	public Object visit(IntLiteral intLiteral) {
		ints.add(intLiteral.getValue());
		return super.visit(intLiteral);
	}

}
