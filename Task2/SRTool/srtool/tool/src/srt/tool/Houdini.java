package srt.tool;

import java.util.List;

import srt.ast.Invariant;
import srt.ast.Program;

public class Houdini {

	private Program p;

	public Houdini(Program p) {
		this.p = p;
	}

	public Program run() {
		CandidateInvariantVisitor v = new CandidateInvariantVisitor();
		p = (Program) v.visit(p);
		List<Invariant> invariants = v.getCandidateInvariants();

		return p;
	}

}
