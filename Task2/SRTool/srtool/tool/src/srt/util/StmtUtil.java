package srt.util;

import java.util.ArrayList;
import java.util.HashSet;
import java.util.List;
import java.util.Set;

import srt.ast.AssignStmt;
import srt.ast.Invariant;
import srt.ast.Node;
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

	public static Set<String> computeModSet(Node node) {
		Set<String> modset = new HashSet<String>();
		if (node == null) {
			return modset;
		}
		if (node instanceof AssignStmt) {
			modset.add(((AssignStmt) node).getLhs().getName());
		} else {
			for (Node child : node.getChildrenCopy()) {
				modset.addAll(computeModSet(child));
			}
		}
		return modset;
	}
}
