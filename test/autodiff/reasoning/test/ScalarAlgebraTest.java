package autodiff.reasoning.test;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.R;
import static autodiff.reasoning.tactics.Auto.autodeduce;
import static autodiff.reasoning.tactics.Stack.*;
import static autodiff.reasoning.test.BasicsTest.build;

import autodiff.reasoning.deductions.Basics;
import autodiff.reasoning.deductions.Propositions;
import autodiff.reasoning.deductions.ScalarAlgebra;
import autodiff.reasoning.deductions.Sets;
import autodiff.reasoning.deductions.Sequences;
import autodiff.reasoning.tactics.Goal;

import org.junit.Test;

/**
 * @author codistmonk (creation 2015-04-13)
 */
public final class ScalarAlgebraTest {
	
	@Test
	public final void test1() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				Basics.setup();
				Sequences.setup();
				Propositions.setup();
				Sets.setup();
				ScalarAlgebra.setup();
				
				final Object _a = $new("a");
				
				suppose($(_a, IN, R));
				
				final Goal goal = Goal.newGoal($($(_a, "+", 1), IN, R));
				
				autodeduce(goal.getProposition());
				
				goal.conclude();
			}
			
		});
	}
	
}
