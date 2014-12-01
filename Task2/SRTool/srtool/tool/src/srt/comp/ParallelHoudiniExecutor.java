package srt.comp;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import srt.ast.Invariant;
import srt.ast.InvariantList;
import srt.ast.Node;
import srt.exec.ProcessExec;
import srt.tool.HoudiniVisitor;
import srt.tool.SRTool.SRToolResult;
import srt.tool.SRToolImpl;
import srt.tool.invgen.CandidateInvariantVisitor;
import srt.tool.invgen.VariableComparisonInvariantInsertVisitor;

public class ParallelHoudiniExecutor {

	private static final Integer INVARIANTS_IN_THREAD = 65;

	private final Integer timeout;
	private boolean ranSuccessfully;
	private InvariantList trueInvariants;

	public ParallelHoudiniExecutor(Integer timeout) {
		this.timeout = timeout;
	}

	public Node run(Node p) {
		p = (Node) (new CandidateInvariantVisitor(p).visit(p));
		List<Invariant> invariants = InvariantCollectorVisitor.run(p);
		System.out.println("Invariants Generated: " + invariants.size());
		List<ProgramVerifyRunnable> programVerifiers = new ArrayList<ProgramVerifyRunnable>();
		ExecutorService executor = Executors.newFixedThreadPool(4);
		for (List<Invariant> invList : splitInvariantList(invariants)) {
			ProgramVerifyRunnable verifyRunnable = new ProgramVerifyRunnable(
					p.withNewChildren(p.getChildrenCopy()), invList);
			programVerifiers.add(verifyRunnable);
			executor.execute(verifyRunnable);
		}
		executor.shutdown();
		while (!executor.isTerminated()) {
			// Wait for executor to finish executing all runnable
			;
		}
		ranSuccessfully = accumulateAllResult(programVerifiers);
		InvariantList trueInvariants = getTrueInvariants(invariants);
		return (Node) new VariableComparisonInvariantInsertVisitor(
				trueInvariants.getInvariants()).visit(p);
	}

	/**
	 * Returns Correct iff all runnabels reported correct.
	 * 
	 * @param programVerifiers
	 * @return
	 */
	private boolean accumulateAllResult(
			List<ProgramVerifyRunnable> programVerifiers) {
		for (ProgramVerifyRunnable p : programVerifiers) {
			if (p.result == SRToolResult.UNKNOWN) {
				return false;
			}
		}
		return true;
	}

	private InvariantList getTrueInvariants(List<Invariant> invariants) {
		List<Invariant> trueInvariants = new ArrayList<Invariant>();
		for (Invariant inv : invariants) {
			if (!inv.isCandidate())
				trueInvariants.add(inv);
		}
		return new InvariantList(trueInvariants);
	}

	private static List<List<Invariant>> splitInvariantList(
			List<Invariant> invariants) {
		List<List<Invariant>> invSplit = new ArrayList<List<Invariant>>();
		for (int i = 0; i <= invariants.size(); i += INVARIANTS_IN_THREAD) {
			int start = i;
			int end = Math.min(start + INVARIANTS_IN_THREAD, invariants.size());
			invSplit.add(invariants.subList(start, end));
		}
		return invSplit;
	}

	private class ProgramVerifyRunnable implements Runnable {

		private Node p;
		private SRToolResult result;

		public ProgramVerifyRunnable(Node p, List<Invariant> invariants) {
			this.p = (Node) new VariableComparisonInvariantInsertVisitor(
					invariants).visit(p);
		}

		@Override
		public void run() {
			// System.out.println("\n\n\n*****Program Text*****\n"
			// + new PrinterVisitor().visit(p) + "\n\n******\n");
			ProcessExec process = SRToolImpl.createZ3Process();
			HoudiniVisitor houdiniVisitor = new HoudiniVisitor(p, process,
					timeout);
			p = (Node) houdiniVisitor.visit(p);
			result = houdiniVisitor.getResult();
		}

	}

	public InvariantList getTrueInvariants() {
		return trueInvariants;
	}

	public boolean ranSuccessfully() {
		return ranSuccessfully;
	}

}
