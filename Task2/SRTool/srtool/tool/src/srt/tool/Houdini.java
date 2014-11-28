package srt.tool;

import java.io.IOException;
import java.util.List;

import srt.ast.Invariant;
import srt.ast.Program;
import srt.exec.ProcessExec;
import srt.tool.SRTool.SRToolResult;
import srt.tool.exception.ProcessTimeoutException;

public class Houdini {

	private Program p;
	private ProcessExec process;
	private Integer timeout;

	public Houdini(Program p, ProcessExec process, Integer timeout) {
		this.p = p;
		this.process = process;
		this.timeout = timeout;
	}

	public Program run() {
		CandidateInvariantVisitor v = new CandidateInvariantVisitor();
		p = (Program) v.visit(p);
		List<Invariant> invariants = v.getCandidateInvariants();
		for (Invariant inv : invariants) {
			// change cand inv to true inv
			inv.setCandidate(false);
			SRToolResult result = verify(p);
			// if program is incorrect then set the inv back to being
			// candidate
			if (result == SRToolResult.INCORRECT) {
				inv.setCandidate(true);
			} else if (result == SRToolResult.UNKNOWN) {
				// TODO: need to see what needs to be done for this case
			}
		}
		return p;
	}

	private SRToolResult verify(Program program) {
		program = (Program) new LoopAbstractionVisitor().visit(program);
		program = (Program) new PredicationVisitor().visit(program);
		program = (Program) new SSAVisitor().visit(program);

		CollectConstraintsVisitor ccv = new CollectConstraintsVisitor();
		ccv.visit(program);
		SMTLIBQueryBuilder builder = new SMTLIBQueryBuilder(ccv);
		builder.buildQuery();

		String smtQuery = builder.getQuery();
		String queryResult = "";
		try {
			queryResult = process.execute(smtQuery, timeout);
		} catch (ProcessTimeoutException e) {
			return SRToolResult.UNKNOWN;
		} catch (IOException e) {
			return SRToolResult.UNKNOWN;
		} catch (InterruptedException e) {
			return SRToolResult.UNKNOWN;
		}
		return SRToolImpl.parseQueryResult(queryResult);
	}

}
