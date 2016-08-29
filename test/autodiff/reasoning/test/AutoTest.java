package autodiff.reasoning.test;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.Goal.*;
import static autodiff.reasoning.tactics.Stack.*;

import org.junit.Test;

import autodiff.reasoning.deductions.Basics;

/**
 * @author codistmonk (creation 2016-08-28)
 */
public final class AutoTest {
	
	@Test
	public final void testAutodeduce1() {
		BasicsTest.build(new Runnable() {
			
			@Override
			public final void run() {
				Basics.setup();
				
				{
					newGoal($($(1, "+", 1), "=", 2));
					
					autodeduce(goal().getProposition());
					
					concludeGoal();
				}
				
				{
					newGoal($rule("a", "a"));
					
					goal().introduce();
					
					autodeduce(goal().getProposition());
					
					concludeGoal();
				}
			}
			
		});
	}
	
	@Test
	public final void testAutobind1() {
		BasicsTest.build(new Runnable() {
			
			@Override
			public final void run() {
				Basics.setup();
				
				suppose(newName(), "condition1");
				
				{
					final Object x = $new("x");
					final Object y = $new("y");
					
					suppose($forall(x,
							$rule("condition1",
									$forall(y,
											"conclusion1"))));
				}
				
				{
					newGoal("conclusion1");
					
					autobind(name(-1), 1, 2);
					
					concludeGoal();
				}
			}
			
		});
	}
	
}
