package autodiff.reasoning.test;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.Goal.*;
import static autodiff.reasoning.tactics.PatternMatching.matchOrFail;
import static autodiff.reasoning.tactics.Stack.*;
import static autodiff.reasoning.test.BasicsTest.build;

import autodiff.reasoning.deductions.ScalarFunctions;
import autodiff.reasoning.tactics.Auto.Simplifier.Mode;

import multij.rules.Variable;

import org.junit.Test;

/**
 * @author codistmonk (creation 2015-04-13)
 */
public final class ScalarFunctionsTest {
	
	@Test
	public final void test1() {
		build(new Runnable() {
			
			@Override
			public final void run() {
				ScalarFunctions.load();
				
				{
					newGoal($($("step_0", -1), "=", 0));
					
					autobindTrim("definition_of_heaviside_function", second(left(goal().getProposition())));
					simplifyCasesInLast();
					
					concludeGoal();
				}
				
				{
					newGoal($($("step_0", 0), "=", 1));
					
					autobindTrim("definition_of_heaviside_function", second(left(goal().getProposition())));
					simplifyCasesInLast();
					
					concludeGoal();
				}
				
				{
					newGoal($($("step_0", 1), "=", 1));
					
					autobindTrim("definition_of_heaviside_function", second(left(goal().getProposition())));
					simplifyCasesInLast();
					
					concludeGoal();
				}
				
				{
					newGoal($($("step_1", -1), "=", 0));
					
					autobindTrim("definition_of_step_1", second(left(goal().getProposition())));
					simplifyCasesInLast();
					
					concludeGoal();
				}
				
				{
					newGoal($($("step_1", 0), "=", 0));
					
					autobindTrim("definition_of_step_1", second(left(goal().getProposition())));
					simplifyCasesInLast();
					
					concludeGoal();
				}
				
				{
					newGoal($($("step_1", 1), "=", 1));
					
					autobindTrim("definition_of_step_1", second(left(goal().getProposition())));
					simplifyCasesInLast();
					
					concludeGoal();
				}
				
				{
					newGoal($($("delta_", $(0, "", 1)), "=", 0));
					
					final Variable vx = v("x");
					final Variable vy = v("y");
					
					matchOrFail($("delta_", $(vx, "", vy)), left(goal().getProposition()));
					
					autobindTrim("definition_of_kronecker_function", vx.get(), vy.get());
					simplifyCasesInLast();
					
					concludeGoal();
				}
				
				{
					newGoal($($("delta_", $(0, "", 0)), "=", 1));
					
					final Variable vx = v("x");
					final Variable vy = v("y");
					
					matchOrFail($("delta_", $(vx, "", vy)), left(goal().getProposition()));
					
					autobindTrim("definition_of_kronecker_function", vx.get(), vy.get());
					simplifyCasesInLast();
					
					concludeGoal();
				}
			}
			
		});
	}
	
	public static final void simplifyCasesInLast() {
		new Simplifier(Mode.DEFINE)
		.add(tryRule((e, m) -> {
			final Variable vx = v("x");
			final Variable vc = v("c");
			
			matchOrFail($("cases", $("", $(vx, "if", vc))), e);
			
			autobindTrim("try_cases_if", vx.get(), vc.get());
		}))
		.add(tryRule((e, m) -> {
			final Variable vx = v("x");
			final Variable vc = v("c");
			final Variable vy = v("y");
			
			matchOrFail($("cases", $("", $(vx, "if", vc), vy)), e);
			
			final Object _x = vx.get();
			final Object _c = vc.get();
			final Object _y = vy.get();
			
			if (tryDeduction(() -> autobindTrim("try_cases_if_stop", _x, _y, _c))) {
				return;
			}
			
			if (tryDeduction(() -> autobindTrim("try_cases_if_not", _x, _y, _c))) {
				return;
			}
			
			fail();
		}))
		.add(tryRule((e, m) -> {
			final Variable vx = v("x");
			
			matchOrFail($("cases", $("", $(vx, "otherwise"))), e);
			
			autobind("try_cases_otherwise", vx.get());
		}))
		.simplifyCompletely(proposition(-1));
	}
	
}
