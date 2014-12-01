package srt.tool.invgen;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.Set;

import srt.ast.AssignStmt;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;
import srt.util.StmtUtil;

public class LoopBodyAssignmentsCollector extends DefaultVisitor {

	private Set<String> loopConditionVariables;
	private Map<String, List<AssignStmt>> assignments;

	public Map<String, List<AssignStmt>> getAssignments() {
		return assignments;
	}

	public LoopBodyAssignmentsCollector(WhileStmt whileStmt) {
		super(false);
		loopConditionVariables = StmtUtil.computeModSet(whileStmt);
		assignments = new HashMap<String, List<AssignStmt>>();
	}

	@Override
	public Object visit(AssignStmt assignStmt) {
		String variableName = assignStmt.getLhs().getName();
		if (loopConditionVariables.contains(variableName)) {
			if (assignments.containsKey(variableName)) {
				assignments.get(variableName).add(assignStmt);
			} else {
				List<AssignStmt> assignStmts = new ArrayList<AssignStmt>();
				assignStmts.add(assignStmt);
				assignments.put(variableName, assignStmts);
			}
		}
		return super.visit(assignStmt);
	}

}
