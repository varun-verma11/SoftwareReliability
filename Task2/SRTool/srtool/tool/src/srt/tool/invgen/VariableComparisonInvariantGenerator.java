package srt.tool.invgen;

import java.util.ArrayList;
import java.util.List;

import srt.ast.DeclRef;
import srt.ast.Invariant;

public class VariableComparisonInvariantGenerator {

	private String[] variableNames;
	private List<Invariant> invariants;

	public VariableComparisonInvariantGenerator(String[] variableNames) {
		this.variableNames = variableNames;
		invariants = null;
	}

	public List<Invariant> generateInvariants() {
		if (invariants != null) {
			return invariants;
		}

		List<Invariant> invariants = new ArrayList<Invariant>();

		// Add invariants for all possible comparisons for every pair of
		// variables.
		for (int i = 0; i < variableNames.length; i++) {
			String v1 = variableNames[i];
			for (int j = 0; j < i; j++) {
				String v2 = variableNames[j];
				if (!v1.equals(v2)) {
					invariants.addAll(ArithmeticInvariantGenerator
							.generateComparisonInvariants(new DeclRef(v1),
									new DeclRef(v2)));
				}
			}
		}
		this.invariants = invariants;
		return invariants;
	}
}
