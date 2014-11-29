package srt.tool;

import java.io.IOException;
import java.util.List;

import srt.ast.Invariant;
import srt.ast.Program;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;
import srt.ast.visitor.impl.PrinterVisitor;
import srt.exec.ProcessExec;
import srt.tool.SRTool.SRToolResult;
import srt.tool.exception.ProcessTimeoutException;
import srt.util.StmtUtil;

public class HoudiniVisitor extends DefaultVisitor {

	private Program p;
	private ProcessExec process;
	private Integer timeout;

	public HoudiniVisitor(Program p, ProcessExec process, Integer timeout) {
		super(true);
		this.p = p;
		this.process = process;
		this.timeout = timeout;
	}

	@Override
	public Object visit(WhileStmt whileStmt) {
		visit(whileStmt.getBody());
		List<Invariant> invariants = StmtUtil.getCandidateInvariants(whileStmt);
		for (Invariant inv : invariants) {
			// change cand inv to true inv
			inv.setCandidate(false);

			SRToolResult result = verify(
					(Program) p.withNewChildren(p.getChildrenCopy()), whileStmt);
			// if program is incorrect then set the invariant back to being
			// candidate
			if (result == SRToolResult.INCORRECT) {
				inv.setCandidate(true);
			} else if (result == SRToolResult.UNKNOWN) {
				// TODO: need to see what needs to be done for this case
				return p;
			}
		}
		return whileStmt;
	}

	private SRToolResult verify(Program program, WhileStmt whileStmt) {
		program = (Program) new AssertionRemoverVisitor().visit(program);
		program = (Program) new LoopAbstractionVisitor().visit(program);
		program = (Program) new PredicationVisitor().visit(program);
		program = (Program) new SSAVisitor().visit(program);

		CollectConstraintsVisitor ccv = new CollectConstraintsVisitor();
		ccv.visit(program);
		SMTLIBQueryBuilder builder = new SMTLIBQueryBuilder(ccv);
		builder.buildQuery();

		String programText = new PrinterVisitor().visit(program);
		// System.out.println("\n\n\n *************** \n\n" + programText
		// + "\n\n\n *************** \n\n");
		// System.out.println("\n\n\n *************** \n\n" + builder.getQuery()
		// + "\n\n\n *************** \n\n");

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
		// System.out.println("\n\n\n *************** \n\n" + queryResult
		// + "\n\n\n *************** \n\n");
		return SRToolImpl.parseQueryResult(queryResult);
	}

}
