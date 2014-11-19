package srt.tool;

import srt.ast.AssertStmt;
import srt.ast.AssignStmt;

public class SMTLIBQueryBuilder
{

    private ExprToSmtlibVisitor exprConverter;
    private CollectConstraintsVisitor constraints;
    private String queryString = "";

    public SMTLIBQueryBuilder(CollectConstraintsVisitor ccv)
    {
        this.constraints = ccv;
        this.exprConverter = new ExprToSmtlibVisitor();
    }

    public void buildQuery()
    {
        StringBuilder query = new StringBuilder();
        query.append("(set-logic QF_BV)\n" //
                + "(declare-sort Int 0)\n" //
                + "(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
        // TODO: Define more functions above (for convenience), as needed.

        // TODO: Declare variables, add constraints, add properties to check
        // here.

        // declare variables
        for (String v : constraints.variableNames)
        {
            query.append("(declare-fun " + v + " () (_ BitVec 32))\n");
        }

        // add constraints for assignment checks
        for (AssignStmt stmt : constraints.transitionNodes)
        {
            query.append("(assert (= " + stmt.getLhs().getName() + " " + exprConverter.visit(stmt.getRhs()) + "))\n");
        }

        {
            // add checks for assertions
            int currentI = 0;
            for (AssertStmt assertStmt : constraints.propertyNodes)
            {
                query.append("(define-fun prop" + currentI + " () Bool (not " + exprConverter.visit(assertStmt.getCondition()) + ") )\n");
                currentI++;
            }

            // add checks for all the properties.
            query.append("(assert ");
            for (int i = 0; i < constraints.propertyNodes.size(); i++)
            {
                query.append("(or prop" + i + "");
            }
            for (int i = 0; i <= constraints.propertyNodes.size(); i++)
            {
                query.append(")");
            }
            query.append("\n");
        }
        query.append("(check-sat)\n");
        buildGetValueProperties(query);
        queryString = query.toString();
    }

    private void buildGetValueProperties(StringBuilder query)
    {
        query.append("(get-value (");
        for (int i = 0; i < constraints.propertyNodes.size(); i++)
        {
            query.append("prop" + i);
            if (i < constraints.propertyNodes.size() - 1)
            {
                query.append(" ");
            }
        }
        query.append("))\n\n");
    }

    public String getQuery()
    {
        return queryString;
    }

}
