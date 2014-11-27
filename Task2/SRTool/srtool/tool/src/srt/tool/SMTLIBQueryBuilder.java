package srt.tool;

import srt.ast.AssertStmt;
import srt.ast.AssignStmt;

public class SMTLIBQueryBuilder {

	private ExprToSmtlibVisitor exprConverter;
	private CollectConstraintsVisitor constraints;
	private String queryString = "";
	private StringBuilder query;

	public static final String TOBOOL = "tobool";
	public static final String TOBV32 = "tobv32";

	public SMTLIBQueryBuilder(CollectConstraintsVisitor ccv) {
		this.constraints = ccv;
		this.exprConverter = new ExprToSmtlibVisitor();
		this.query = new StringBuilder();
	}

	public void buildQuery() {
		appendToQuery("(set-logic QF_BV)\n");
		appendToQuery(
				"(define-fun %s ((p (_ BitVec 32))) Bool (not (= p (_ bv0 32))))\n",
				TOBOOL);
		appendToQuery(
				"(define-fun %s ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n",
				TOBV32);

		// Declare variables.
		for (String v : constraints.variableNames) {
			appendToQuery("(declare-fun %s () (_ BitVec 32))\n", v);
		}

		// Add constraints for assignment checks.
		for (AssignStmt stmt : constraints.transitionNodes) {
			appendToQuery("(assert (= %s %s ))\n", stmt.getLhs().getName(),
					exprConverter.visit(stmt.getRhs()));
		}

		handleAssertions();

		appendToQuery("(check-sat)\n");
		buildGetValueProperties();
		queryString = query.toString();
	}

	private void handleAssertions() {
		// If there are no assertions in the program, we need the SAT program
		// to be unsatisfiable, so we append an artificial assert false.
		if (constraints.propertyNodes.size() == 0) {
			appendToQuery("(assert false)\n");
			return;
		}

		// Add checks for assertions.
		int currentI = 0;
		for (AssertStmt assertStmt : constraints.propertyNodes) {
			appendToQuery("(define-fun prop%s () Bool (not (%s %s)))\n",
					String.valueOf(currentI), TOBOOL,
					exprConverter.visit(assertStmt.getCondition()));
			currentI++;
		}

		// Add checks for all the properties.
		if (constraints.propertyNodes.size() > 0) {
			appendToQuery("(assert ");
			for (int i = 0; i < constraints.propertyNodes.size(); i++) {
				appendToQuery("(or prop%s", String.valueOf(i));
			}
			for (int i = 0; i <= constraints.propertyNodes.size(); i++) {
				appendToQuery(")");
			}
			appendToQuery("\n");
		}
	}

	private void buildGetValueProperties() {
		if (constraints.propertyNodes.size() == 0) {
			return;
		}
		appendToQuery("(get-value (");
		for (int i = 0; i < constraints.propertyNodes.size(); i++) {
			appendToQuery("prop%s", String.valueOf(i));
			if (i < constraints.propertyNodes.size() - 1) {
				appendToQuery(" ");
			}
		}
		appendToQuery("))\n\n");
	}

	private void appendToQuery(String s, Object... args) {
		query.append(String.format(s, args));
	}

	public String getQuery() {
		return queryString;
	}

}
