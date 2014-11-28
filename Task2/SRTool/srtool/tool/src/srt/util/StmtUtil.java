package srt.util;

import java.util.ArrayList;
import java.util.List;

import srt.ast.Invariant;
import srt.ast.WhileStmt;

public class StmtUtil {

	public static List<Invariant> getCandidateInvariants(WhileStmt whileStmt) {
		List<Invariant> candInvariants = new ArrayList<Invariant>();
		for (Invariant i : whileStmt.getInvariantList().getInvariants()) {
			if (i.isCandidate()) {
				candInvariants.add(i);
			}
		}
		return candInvariants;
	}

	public static List<Invariant> getTrueInvariants(WhileStmt whileStmt) {
		List<Invariant> trueInvariants = new ArrayList<Invariant>();
		for (Invariant i : whileStmt.getInvariantList().getInvariants()) {
			if (!i.isCandidate()) {
				trueInvariants.add(i);
			}
		}
		return trueInvariants;
	}
}
