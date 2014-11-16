package srt.tool;

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
                + "(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n" //
                + "(define-fun tobv32 ((p Bool)) (_ BitVec 32) (ite p (_ bv1 32) (_ bv0 32)))\n");
        // TODO: Define more functions above (for convenience), as needed.

        // TODO: Declare variables, add constraints, add properties to check
        // here.

        // declare variables
        for (String v : constraints.variableNames)
        {
            query.append("(declare-fun " + v + " () (BitVec 32))\n");
        }

        // add constraints
        for (AssignStmt stmt : constraints.transitionNodes)
        {
            query.append("assert (bv32tobool " + exprConverter.visit(stmt) + "))\n");
        }

        // add properties
        {
            String props = "";
            for (int i = 0; i < constraints.propertyNodes.size(); i++)
            {
                props += "(declare-fun prop" + i + " () (Bool))\n";
            }

            for (int i = 0; i < constraints.propertyNodes.size(); i++)
            {
                props += "(assert  (= prop" + i + " (not (bv32tobool " + exprConverter.visit(constraints.propertyNodes.get(i)) + "))))\n";
            }

            props += "(assert (or ";
            for (int i = 0; i < constraints.propertyNodes.size(); i++)
            {
                props += "prop" + i + " ";
            }
            props = props.trim() + ("))\n"); // performance
            query.append(props);
        }

        query.append("(check-sat)\n");
        queryString = query.toString();
    }

    public String getQuery()
    {
        return queryString;
    }

}
