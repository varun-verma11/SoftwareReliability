package srt.tool;

import java.io.IOException;

import srt.ast.Program;
import srt.ast.visitor.impl.PrinterVisitor;
import srt.comp.IterativeInvariantGeneration;
import srt.exec.ProcessExec;
import srt.tool.exception.ProcessTimeoutException;
import srt.tool.invgen.CandidateInvariantVisitor;

public class SRToolImpl implements SRTool {
	private Program program;
	private CLArgs clArgs;

	public SRToolImpl(Program p, CLArgs clArgs) {
		this.program = p;
		this.clArgs = clArgs;
	}

	public SRToolResult go() throws IOException, InterruptedException {
		long start = System.currentTimeMillis();
		// TODO: Transform program using Visitors here.

		// You can use other solvers.
		// E.g. The command for cvc4 is: "cvc4", "--lang", "smt2"
		// create the process to call z3 solver
		ProcessExec process = createZ3Process();

		if (clArgs.mode.equals(CLArgs.COMP)) {
			IterativeInvariantGeneration iterativeInvariantGernation = new IterativeInvariantGeneration(
					clArgs.timeout);
			iterativeInvariantGernation.visit(program);
		}

		String programText;

		boolean invgenMode = clArgs.mode.equals(CLArgs.INVGEN);
		if (clArgs.mode.equals(CLArgs.HOUDINI) || invgenMode) {
			if (invgenMode) {
				program = (Program) new CandidateInvariantVisitor(program)
						.visit(program);
			}
			program = (Program) new HoudiniVisitor(program, process,
					clArgs.timeout).visit(program);
		}
		if (clArgs.mode.equals(CLArgs.BMC)) {
			program = (Program) new LoopUnwinderVisitor(clArgs.unsoundBmc,
					clArgs.unwindDepth).visit(program);
		} else {
			program = (Program) new LoopAbstractionVisitor().visit(program);
		}
		program = (Program) new PredicationVisitor().visit(program);
		program = (Program) new SSAVisitor().visit(program);

		// Output the program as text after being transformed (for debugging).
		if (clArgs.verbose) {
			programText = new PrinterVisitor().visit(program);
			System.out.println(programText);
		}

		// Collect the constraint expressions and variable names.
		CollectConstraintsVisitor ccv = new CollectConstraintsVisitor();
		ccv.visit(program);

		// Convert constraints to SMTLIB String.
		SMTLIBQueryBuilder builder = new SMTLIBQueryBuilder(ccv);
		builder.buildQuery();

		String smtQuery = builder.getQuery();

		// Output the query for debugging
		if (clArgs.verbose) {
			System.out.println(smtQuery);
		}

		// Submit query to SMT solver.
		String queryResult = "";
		try {
			queryResult = process.execute(smtQuery, clArgs.timeout);
		} catch (ProcessTimeoutException e) {
			if (clArgs.verbose) {
				System.out.println("Timeout!");
			}
			return SRToolResult.UNKNOWN;
		}

		// output query result for debugging
		if (clArgs.verbose) {
			System.out.println(queryResult);
		}
		System.out.println("Time taken: "
				+ (System.currentTimeMillis() - start) + "ms");
		return parseQueryResult(queryResult);
	}

	public static ProcessExec createZ3Process() {
		return new ProcessExec("z3", "-smt2", "-in");
	}

	public static SRToolResult parseQueryResult(String queryResult) {
		if (queryResult.startsWith("unsat")) {
			return SRToolResult.CORRECT;
		}

		if (queryResult.startsWith("sat")) {
			return SRToolResult.INCORRECT;
		}

		// query result started with something other than "sat" or "unsat"
		return SRToolResult.UNKNOWN;
	}
}
