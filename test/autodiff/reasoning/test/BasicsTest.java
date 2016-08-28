package autodiff.reasoning.test;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.Stack.*;
import static multij.tools.Tools.*;

import autodiff.reasoning.deductions.Basics;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.tactics.Goal;

import org.junit.Test;

/**
 * @author codistmonk (creation 2015-04-13)
 */
public final class BasicsTest {
	
	@Test
	public final void testRewrite() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				supposeRewrite();
				
				suppose($equality("a", "b"));
				
				final Goal goal = Goal.newGoal($equality("b", "b"));
				
				rewrite(name(-1), name(-1));
				
				goal.conclude();
			}
			
		});
	}
	
	@Test
	public final void testRewriteRight() {
		build(() -> {
			supposeRewrite();
			deduceIdentity();
			deduceCommutativityOfEquality();
			
			suppose($equality("a", "b"));
			
			final Goal goal = Goal.newGoal($equality("a", "a"));
			
			rewriteRight(name(-1), name(-1));
			
			goal.conclude();
		});
	}
	
	@Test
	public final void testDeduceIdentity() {
		build(() -> {
			supposeRewrite();
			deduceIdentity();
			
			final Goal goal = Goal.newGoal($equality("a", "a"));
			
			bind("identity", $("a"));
			
			goal.conclude();
		});
	}
	
	@Test
	public final void testDeduceRecall() {
		build(() -> {
			supposeRewrite();
			deduceIdentity();
			deduceRecall();
			
			suppose($("a"));
			
			final Goal goal = Goal.newGoal($rule("a", "a"));
			
			bind("recall", $("a"));
			
			goal.conclude();
		});
	}
	
	public static final Deduction build(final Runnable deductionBuilder) {
		return build(getCallerMethodName(), deductionBuilder, 1);
	}
	
	public static final Deduction build(final String deductionName, final Runnable deductionBuilder, final int debugDepth) {
		return Basics.build(deductionName, deductionBuilder, debugDepth);
	}
	
}
