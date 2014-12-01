package srt.tool.invgen;

import java.util.ArrayList;
import java.util.List;

import srt.ast.BinaryExpr;
import srt.ast.Expr;
import srt.ast.Invariant;

public class ArithmeticInvariantGenerator {

	/** Generates invariants comparing between the given LHS and RHS. */
	public static List<Invariant> generateComparisonInvariants(Expr lhs,
			Expr rhs) {
		List<Invariant> invs = new ArrayList<Invariant>();
		invs.add(createBinaryInvariant(BinaryExpr.EQUAL, lhs, rhs));
		invs.add(createBinaryInvariant(BinaryExpr.NEQUAL, lhs, rhs));
		invs.add(createBinaryInvariant(BinaryExpr.GEQ, lhs, rhs));
		invs.add(createBinaryInvariant(BinaryExpr.GT, lhs, rhs));
		invs.add(createBinaryInvariant(BinaryExpr.LT, lhs, rhs));
		invs.add(createBinaryInvariant(BinaryExpr.LEQ, lhs, rhs));
		return invs;
	}

	private static Invariant createBinaryInvariant(int operator, Expr lhs,
			Expr rhs) {
		return new Invariant(true, new BinaryExpr(operator, lhs, rhs));
	}
}
