package srt.comp;

import java.util.ArrayList;
import java.util.List;

import srt.ast.AssignStmt;
import srt.ast.AssumeStmt;
import srt.ast.BlockStmt;
import srt.ast.Decl;
import srt.ast.EmptyStmt;
import srt.ast.IfStmt;
import srt.ast.Stmt;
import srt.ast.UnaryExpr;
import srt.ast.WhileStmt;
import srt.ast.visitor.impl.DefaultVisitor;
import srt.tool.LoopAbstractionVisitor;

public class IterativeInvariantGeneration extends DefaultVisitor {

	private List<Stmt> stmtAccumulator = new ArrayList<Stmt>();
	private boolean isCorrect = true;
	private Integer timeout;

	public IterativeInvariantGeneration(Integer timeout) {
		super(true);
		this.timeout = timeout;
	}

	@Override
	public Object visit(AssignStmt stmt) {
		stmtAccumulator.add(stmt);
		return super.visit(stmt);
	}

	@Override
	public Object visit(AssumeStmt stmt) {
		stmtAccumulator.add(stmt);
		return super.visit(stmt);
	}

	@Override
	public Object visit(Decl stmt) {
		stmtAccumulator.add(stmt);
		return super.visit(stmt);
	}

	// Recursively iterate through the body to ensure we get to the first
	// nested loop in the program.
	// To get S' in program below, we make a new instance of visitor
	// S
	// L {S'L' T'}
	// T
	@Override
	public Object visit(WhileStmt stmt) {
		System.out.println("Entering While Now!!!");
		IterativeInvariantGeneration bodyVisitor = new IterativeInvariantGeneration(
				timeout);
		bodyVisitor.stmtAccumulator.addAll(stmtAccumulator);

		Stmt newBody = (Stmt) bodyVisitor.visit(stmt.getBody());
		if (!bodyVisitor.isCorrect) {
			// some problem while proving the body of the loop so we stop here
			this.isCorrect = false;
			System.out.println("****Exiting Loop due to some nested fail****");
			return new EmptyStmt();
		}
		WhileStmt loopFreeWhile = new WhileStmt(stmt.getCondition(),
				stmt.getBound(), stmt.getInvariantList(), newBody);

		// Make a new program with accumulated stmts and new while without loops
		List<Stmt> stmts = new ArrayList<Stmt>(stmtAccumulator);
		stmts.add(loopFreeWhile);

		ParallelHoudiniExecutor parallelHoudini = new ParallelHoudiniExecutor(
				timeout);
		parallelHoudini.run(new BlockStmt(stmts));
		if (!parallelHoudini.ranSuccessfully()) {
			isCorrect = false;
			System.out.println("****Exiting Loop due to houdini fail****");
			return new EmptyStmt();
		}

		// Get rid of the loop and add the conditional
		LoopAbstractionVisitor loopAV = new LoopAbstractionVisitor();
		List<Stmt> flattenedWhile = ((BlockStmt) loopAV.visit(stmt))
				.getStmtList().getStatements();
		// Add assume of loop wasn't done
		IfStmt ifStmt = ((IfStmt) flattenedWhile.get(flattenedWhile.size() - 1));
		flattenedWhile.add(new AssumeStmt(new UnaryExpr(UnaryExpr.LNOT, ifStmt
				.getCondition())));
		flattenedWhile.remove(flattenedWhile.size() - 2);

		stmtAccumulator.addAll(flattenedWhile);
		System.out.println("Exiting While Now: End");
		return new BlockStmt(flattenedWhile);
	}
}
