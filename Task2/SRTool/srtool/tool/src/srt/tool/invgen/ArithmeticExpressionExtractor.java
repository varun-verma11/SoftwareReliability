package srt.tool.invgen;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import srt.ast.BinaryExpr;
import srt.ast.DeclRef;
import srt.ast.Expr;
import srt.ast.Invariant;
import srt.ast.Node;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;
import srt.util.StmtUtil;

public class ArithmeticExpressionExtractor {

	public List<Invariant> generateArithmeticCandidates(WhileStmt whileStmt) {
		ArithmeticExpressionVisitor v = new ArithmeticExpressionVisitor(
				whileStmt);
		v.visit(whileStmt.getCondition());
		List<Invariant> candidateInvariants = new ArrayList<Invariant>();

		for (Expr expr : v.getExpr()) {
			candidateInvariants.addAll(ArithmeticInvariantGenerator
					.generateInvariants(expr));
		}
		return candidateInvariants;
	}

	private class ArithmeticExpressionVisitor extends DefaultVisitor {
		private List<Expr> expr;
		private Set<String> modset;

		public ArithmeticExpressionVisitor(WhileStmt whileStmt) {
			super(false);
			expr = new ArrayList<Expr>();
			this.modset = StmtUtil.computeModSet(whileStmt);
		}

		@Override
		public Object visit(BinaryExpr binaryExpr) {
			if (isInModset(binaryExpr.getLhs())
					|| isInModset(binaryExpr.getRhs())) {
				expr.add(binaryExpr);
			}
			return super.visit(binaryExpr);
		}

		private boolean isInModset(Node node) {
			if (!(node instanceof DeclRef)) {
				return false;
			}
			DeclRef declRef = (DeclRef) node;
			if (modset.contains(declRef.getName())) {
				return true;
			} else {
				return false;
			}
		}

		public List<Expr> getExpr() {
			return expr;
		}
	}

}
