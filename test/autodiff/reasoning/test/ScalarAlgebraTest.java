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
import multij.tools.Tools;

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
	public final void testCanonicalizeAdditionAssociativity1() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarAlgebra.load();
				
				/*
				 * 
				 * (x+y)+z   -> x+(y+z)
				 * ax+(bx+z) -> (a+b)x+z
				 * ax+(x+z)  -> (a+1)x+z
				 * x+(bx+z)  -> (1+b)x+z
				 * x+(x+z)   -> (1+1)x+z
				 * by+(ax+z) -> ax+(by+z)
				 * y+(ax+z)  -> ax+(y+z)
				 * by+(x+z)  -> x+(by+z)
				 * y+(x+z)   -> x+(y+z)
				 * 
				 */
				
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _z = $new("z");
				
				suppose($(_x, IN, R));
				suppose($(_y, IN, R));
				suppose($(_z, IN, R));
				
				final int a = 5;
				final int b = 2;
				final Object _a = $(a);
				final Object _b = $(b);
				final Object _ax = $(_a, "*", _x);
				final Object _bx = $(_b, "*", _x);
				final Object _by = $(_b, "*", _y);
				
				testCanonicalize(
						$($(_x, "+", _y), "+", _z),
						$(_x, "+", $(_y, "+", _z)));
				testCanonicalize(
						$(_ax, "+", $(_bx, "+", _z)),
						$($($(a + b), "*", _x), "+", _z));
				testCanonicalize(
						$(_ax, "+", $(_x, "+", _z)),
						$($($(a + 1), "*", _x), "+", _z));
				testCanonicalize(
						$(_x, "+", $(_bx, "+", _z)),
						$($($(1 + b), "*", _x), "+", _z));
				testCanonicalize(
						$(_x, "+", $(_x, "+", _z)),
						$($($(1 + 1), "*", _x), "+", _z));
				testCanonicalize(
						$(_by, "+", $(_ax, "+", _z)),
						$(_ax, "+", $(_by, "+", _z)));
				testCanonicalize(
						$(_y, "+", $(_ax, "+", _z)),
						$(_ax, "+", $(_y, "+", _z)));
				testCanonicalize(
						$(_by, "+", $(_x, "+", _z)),
						$(_x, "+", $(_by, "+", _z)));
				testCanonicalize(
						$(_y, "+", $(_x, "+", _z)),
						$(_x, "+", $(_y, "+", _z)));
			}
			
		}, new Simple(1));
	}
	
	@Test
	public final void testCanonicalizeMultiplicationAssociativity1() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarAlgebra.load();
				
				/*
				 * 
				 * (x*y)*z     -> x*(y*z)
				 * x^a*(x^b*z) -> x^(a+b)*z
				 * x^a*(x*z)   -> x^(a+1)*z
				 * x*(x^b*z)   -> x^(1+b)*z
				 * x*(x*z)     -> x^(1+1)*z
				 * y*(x*z)     -> x*(y*z)
				 * 
				 */
				
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _z = $new("z");
				
				suppose($(_x, IN, R));
				suppose($(_y, IN, R));
				suppose($(_z, IN, R));
				
				final int a = 2;
				final int b = 5;
				final Object _a = $(a);
				final Object _b = $(b);
				final Object _xa = $(_x, "^", _a);
				final Object _xb = $(_x, "^", _b);
				
				testCanonicalize(
						$($(_x, "*", _y), "*", _z),
						$(_x, "*", $(_y, "*", _z)));
				testCanonicalize(
						$(_xa, "*", $(_xb, "*", _z)),
						$($(_x, "^", $(a + b)), "*", _z));
				testCanonicalize(
						$(_xa, "*", $(_x, "*", _z)),
						$($(_x, "^", $(a + 1)), "*", _z));
				testCanonicalize(
						$(_x, "*", $(_xb, "*", _z)),
						$($(_x, "^", $(1 + b)), "*", _z));
				testCanonicalize(
						$(_x, "*", $(_x, "*", _z)),
						$($(_x, "^", $(1 + 1)), "*", _z));
				testCanonicalize(
						$(_y, "*", $(_x, "*", _z)),
						$(_x, "*", $(_y, "*", _z)));
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
