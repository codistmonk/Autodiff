package autodiff.reasoning.test;

import static autodiff.reasoning.deductions.ScalarAlgebra.canonicalize;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.tactics.Auto.autodeduce;
import static autodiff.reasoning.tactics.Goal.newGoal;
import static autodiff.reasoning.tactics.Stack.*;
import static autodiff.reasoning.test.BasicsTest.build;

import autodiff.reasoning.deductions.ScalarAlgebra;
import autodiff.reasoning.io.Simple;
import autodiff.reasoning.tactics.Goal;

import org.junit.Test;

/**
 * @author codistmonk (creation 2015-04-13)
 */
public final class ScalarAlgebraTest {
	
	@Test
	public final void testAutodeduce1() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarAlgebra.load();
				
				final Object _a = $new("a");
				
				suppose($(_a, IN, R));
				
				testAutodeduce($($(_a, "+", 1), IN, R));
				testAutodeduce($($(_a, "*", 1), IN, R));
				testAutodeduce($($(_a, "-", 1), IN, R));
				testAutodeduce($($(_a, "/", 1), IN, R));
			}
			
		});
	}
	
	@Test
	public final void testAutodeduce2() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarAlgebra.load();
				
				final Object _a = $new("a");
				
				suppose($(_a, IN, N));
				
				testAutodeduce($($(_a, "+", 1), IN, R));
			}
			
		});
	}
	
	@Test
	public final void testAutodeduce3() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarAlgebra.load();
				
				final Object _a = $new("a");
				final Object _b = $new("b");
				
				suppose($(_a, IN, R));
				suppose($(_b, IN, N));
				
				testAutodeduce($($($($(_a, "+", 1), "*", $(_b, "-", 2)), "/", 6), IN, R));
			}
			
		});
	}
	
	@Test
	public final void testCanonicalize1() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarAlgebra.load();
				
				final Object _a = $new("a");
				final Object _b = $new("b");
				
				suppose($(_a, IN, R));
				suppose($(_b, IN, N));
				
				testCanonicalize($(_a, "+", $(1, "+", 1)), $(2, "+", _a));
				testCanonicalize($(_a, "+", _a), $(2, "*", _a));
				testCanonicalize($(_a, "+", $(2, "*", _a)), $(3, "*", _a));
				testCanonicalize($(_a, "+", 0), _a);
				testCanonicalize($(_a, "-", _a), 0);
				testCanonicalize($(_a, "+", $(_b, "+", _a)), $($(2, "*", _a), "+", _b));
			}
			
		}, new Simple(1));
	}
	
	@Test
	public final void testCanonicalize2() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarAlgebra.load();
				
				final Object _a = $new("a");
				final Object _b = $new("b");
				
				suppose($(_a, IN, R));
				suppose($(_b, IN, N));
				
				testCanonicalize($(_a, "*", _a), $(_a, "^", 2));
				testCanonicalize($(_a, "*", $(_a, "^", 2)), $(_a, "^", 3));
				testCanonicalize($(_b, "*", _a), $(_a, "*", _b));
			}
			
		}, new Simple(1));
	}
	
	public static final void testCanonicalize(final Object expression, final Object expectedCanonicalized) {
		final Goal goal = newGoal($(expression, "=", expectedCanonicalized));
		
		canonicalize(left(goal.getProposition()));
		
		goal.conclude();
	}
	
	public static final void testAutodeduce(final Object proposition) {
		final Goal goal = newGoal(proposition);
		
		autodeduce(goal.getProposition());
		
		goal.conclude();
	}
	
}
