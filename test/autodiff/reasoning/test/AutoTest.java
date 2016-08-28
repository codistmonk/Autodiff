package autodiff.reasoning.test;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.Goal.*;

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
	
}
