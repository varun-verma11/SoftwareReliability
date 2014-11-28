package srt.tool;

import java.util.ArrayList;
import java.util.List;

import srt.ast.Invariant;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;
import srt.util.StmtUtil;

public class CandidateInvariantVisitor extends DefaultVisitor {

	private List<Invariant> candidateInvariants;

	public CandidateInvariantVisitor() {
		super(false);
		candidateInvariants = new ArrayList<Invariant>();
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		candidateInvariants.addAll(StmtUtil.getCandidateInvariants(whileStmt));
		visit(whileStmt.getBody());
		return whileStmt;
	}

	public List<Invariant> getCandidateInvariants() {
		return candidateInvariants;
	}
}
