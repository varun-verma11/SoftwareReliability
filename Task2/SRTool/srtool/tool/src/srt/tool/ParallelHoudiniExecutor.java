package srt.tool;

import java.util.ArrayList;
import java.util.List;
import java.util.concurrent.ExecutorService;
import java.util.concurrent.Executors;

import srt.ast.Invariant;
import srt.ast.Program;
import srt.exec.ProcessExec;

public class ParallelHoudiniExecutor {

	private static final Integer INVARIANTS_IN_THREAD = 65;

	private final Integer timeout;

	public ParallelHoudiniExecutor(Integer timeout) {
		this.timeout = timeout;
	}

	public Program run(Program p, List<Invariant> invariants) {
		List<ProgramVerifyRunnable> programVerifiers = new ArrayList<ProgramVerifyRunnable>();
		ExecutorService executor = Executors.newFixedThreadPool(4);
		for (List<Invariant> invList : splitInvariantList(invariants)) {
			ProgramVerifyRunnable verifyRunnable = new ProgramVerifyRunnable(
					(Program) p.withNewChildren(p.getChildrenCopy()), invList);
			programVerifiers.add(verifyRunnable);
			executor.execute(verifyRunnable);
		}
		executor.shutdown();
		while (!executor.isTerminated()) {
			// Wait for executor to finish executing all runnable
			;
		}
		List<Invariant> trueInvariants = getTrueInvariants(invariants);
		return (Program) new CandidateInvariantInsertVisitor(trueInvariants)
				.visit(p);
	}

	private List<Invariant> getTrueInvariants(List<Invariant> invariants) {
		List<Invariant> trueInvariants = new ArrayList<Invariant>();
		for (Invariant inv : invariants) {
			if (!inv.isCandidate())
				trueInvariants.add(inv);
		}
		return trueInvariants;
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

		private Program p;

		public ProgramVerifyRunnable(Program p, List<Invariant> invariants) {
			this.p = (Program) new CandidateInvariantInsertVisitor(invariants)
					.visit(p);
		}

		@Override
		public void run() {
			ProcessExec process = SRToolImpl.createZ3Process();
			p = (Program) new HoudiniVisitor(p, process, timeout).visit(p);
		}

	}

}
