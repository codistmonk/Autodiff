package autodiff.reasoning.test;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.tactics.Auto.autodeduce;
import static autodiff.reasoning.tactics.Goal.newGoal;
import static autodiff.reasoning.tactics.Stack.*;
import static autodiff.reasoning.test.BasicsTest.build;
import static multij.tools.Tools.*;

import java.io.FileNotFoundException;
import java.io.PrintStream;

import autodiff.reasoning.deductions.ScalarAlgebra;
import autodiff.reasoning.io.HTML;
import autodiff.reasoning.io.Simple;
import autodiff.reasoning.proofs.Deduction;
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
				ScalarAlgebra.load();
				
				final Object _a = $new("a");
				
				suppose($(_a, IN, R));
				
				{
					final Goal goal = newGoal($($(_a, "+", 1), IN, R));
					
					autodeduce(goal.getProposition());
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($(_a, "*", 1), IN, R));
					
					autodeduce(goal.getProposition());
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($(_a, "-", 1), IN, R));
					
					autodeduce(goal.getProposition());
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($(_a, "/", 1), IN, R));
					
					autodeduce(goal.getProposition());
					
					goal.conclude();
				}
			}
			
		});
	}
	
	@Test
	public final void test2() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarAlgebra.load();
				
				final Object _a = $new("a");
				
				suppose($(_a, IN, N));
				
				final Goal goal = newGoal($($(_a, "+", 1), IN, R));
				
				autodeduce(goal.getProposition());
				
				goal.conclude();
			}
			
		});
	}
	
	@Test
	public final void test3() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarAlgebra.load();
				
				final Object _a = $new("a");
				final Object _b = $new("b");
				
				suppose($(_a, IN, R));
				suppose($(_b, IN, N));
				
				final Goal goal = newGoal($($($($(_a, "+", 1), "*", $(_b, "-", 2)), "/", 6), IN, R));
				
				autodeduce(goal.getProposition());
				
				goal.conclude();
			}
			
		});
	}
	
	@Test
	public final void testCanonicalize1() throws FileNotFoundException {
		if (false) {
			final Deduction.Processor printer = new HTML().setOutput(new PrintStream(getThisMethodName() + ".html"));
		}
		
		final Deduction.Processor printer = new Simple(1);
		final Deduction deduction = build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarAlgebra.load();
				
				final Object _a = $new("a");
				final Object _b = $new("b");
				
				suppose($(_a, IN, R));
				suppose($(_b, IN, N));
				
				{
					final Goal goal = newGoal($($($($(_a, "+", 1), "*", $(_b, "-", 2)), "/", 6), IN, R));
					
					autodeduce(goal.getProposition());
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($(_a, "+", $(1, "+", 1)), "=", $(2, "+", _a)));
					
					bind("identity", left(goal.getProposition()));
					ScalarAlgebra.CANONICALIZER.simplifyCompletely(proposition(-1));
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($(_a, "+", _a), "=", $(2, "*", _a)));
					
					bind("identity", left(goal.getProposition()));
					ScalarAlgebra.CANONICALIZER.simplifyCompletely(proposition(-1));
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($(_a, "+", $(2, "*", _a)), "=", $(3, "*", _a)));
					
					bind("identity", left(goal.getProposition()));
					ScalarAlgebra.CANONICALIZER.simplifyCompletely(proposition(-1));
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($($(2, "*", _a), "+", _a), "=", $(3, "*", _a)));
					
					bind("identity", left(goal.getProposition()));
					ScalarAlgebra.CANONICALIZER.simplifyCompletely(proposition(-1));
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($(_b, "+", _a), "=", $(_a, "+", _b)));
					
					bind("identity", left(goal.getProposition()));
					ScalarAlgebra.CANONICALIZER.simplifyCompletely(proposition(-1));
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($(_a, "*", _a), "=", $(_a, "^", 2)));
					
					bind("identity", left(goal.getProposition()));
					ScalarAlgebra.CANONICALIZER.simplifyCompletely(proposition(-1));
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($(_a, "*", $(_a, "^", 2)), "=", $(_a, "^", 3)));
					
					bind("identity", left(goal.getProposition()));
					ScalarAlgebra.CANONICALIZER.simplifyCompletely(proposition(-1));
					
					goal.conclude();
				}
				
				{
					final Goal goal = newGoal($($(_b, "*", _a), "=", $(_a, "*", _b)));
					
					bind("identity", left(goal.getProposition()));
					ScalarAlgebra.CANONICALIZER.simplifyCompletely(proposition(-1));
					
					goal.conclude();
				}
			}
			
		}, printer);
		
		printer.process(deduction);
	}
	
}
