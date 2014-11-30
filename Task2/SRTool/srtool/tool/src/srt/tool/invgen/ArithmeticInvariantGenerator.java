package srt.tool.invgen;

import java.util.ArrayList;
import java.util.List;

import srt.ast.BinaryExpr;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.Invariant;

public class ArithmeticInvariantGenerator {

	public static List<Invariant> generateInvariants(Expr expr) {
		if (expr instanceof BinaryExpr) {
			return generateInvariants((BinaryExpr) expr);
		}
		return new ArrayList<Invariant>();
	}

	private static List<Invariant> generateInvariants(BinaryExpr expr) {
		List<Invariant> invs = new ArrayList<Invariant>();
		int operator = expr.getOperator();
		Expr lhs = expr.getLhs();
		Expr rhs = expr.getRhs();

		switch (operator) {
		case BinaryExpr.EQUAL:
		case BinaryExpr.NEQUAL:
		case BinaryExpr.GEQ:
		case BinaryExpr.GT:
		case BinaryExpr.LT:
		case BinaryExpr.LEQ:
			invs.add(createBinaryInvariant(BinaryExpr.EQUAL, lhs, rhs));
			invs.add(createBinaryInvariant(BinaryExpr.NEQUAL, lhs, rhs));
			invs.add(createBinaryInvariant(BinaryExpr.GEQ, lhs, rhs));
			invs.add(createBinaryInvariant(BinaryExpr.GT, lhs, rhs));
			invs.add(createBinaryInvariant(BinaryExpr.LT, lhs, rhs));
			invs.add(createBinaryInvariant(BinaryExpr.LEQ, lhs, rhs));
		}
		return invs;
	}

	public static List<Invariant> generateAssignmentInvariants(
			String variableName, Expr expr) {
		List<Invariant> invs = new ArrayList<Invariant>();
		invs.add(createAssignmentInvariant(BinaryExpr.EQUAL, variableName, expr));
		invs.add(createAssignmentInvariant(BinaryExpr.NEQUAL, variableName,
				expr));
		invs.add(createAssignmentInvariant(BinaryExpr.GEQ, variableName, expr));
		invs.add(createAssignmentInvariant(BinaryExpr.GT, variableName, expr));
		invs.add(createAssignmentInvariant(BinaryExpr.LT, variableName, expr));
		invs.add(createAssignmentInvariant(BinaryExpr.LEQ, variableName, expr));
		return invs;
	}

	private static Invariant createBinaryInvariant(int operator, Expr lhs,
			Expr rhs) {
		return new Invariant(true, new BinaryExpr(operator, lhs, rhs));
	}

	private static Invariant createAssignmentInvariant(int operator,
			String variableName, Expr expr) {
		return new Invariant(true, new BinaryExpr(operator, new DeclRef(
				variableName), expr));
	}
}
