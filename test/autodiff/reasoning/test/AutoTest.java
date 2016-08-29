package autodiff.reasoning.test;

import static autodiff.reasoning.deductions.Sets.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.Goal.*;
import static autodiff.reasoning.tactics.Stack.*;

import autodiff.reasoning.deductions.Basics;
import autodiff.reasoning.deductions.Propositions;
import autodiff.reasoning.deductions.Sequences;
import autodiff.reasoning.deductions.Sets;

import org.junit.Test;

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
	public final void testAutodeduce2() {
		BasicsTest.build(new Runnable() {
			
			@Override
			public final void run() {
				Basics.setup();
				
				Sequences.setup();
				Propositions.setup();
				Sets.setup();
				
				{
					newGoal($(N, SUBSET, R));
					
					autodeduce(goal().getProposition());
					
					concludeGoal();
				}
				
				{
					final Object _x = $new("x");
					
					newGoal($rule($(_x, IN, N), $(_x, IN, Q)));
					
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
	
	@Test
	public final void testAutobind2() {
		BasicsTest.build(new Runnable() {
			
			@Override
			public final void run() {
				Basics.setup();
				
				Sequences.setup();
				Propositions.setup();
				Sets.setup();
				
				{
					final Object x = $new("x");
					
					suppose($(FORALL, x, IN, N, "conclusion1"));
				}
				
				{
					newGoal("conclusion1");
					
					autobind(name(-1), 42);
					autoapply(name(-1));
					
					concludeGoal();
				}
				
				{
					final Object x = $new("x");
					final Object y = $new("y");
					
					suppose($(FORALL, x, ",", y, IN, N, "conclusion2"));
				}
				
				{
					newGoal("conclusion2");
					
					autobind(name(-1), 42, 43);
					autoapply(name(-1));
					
					concludeGoal();
				}
			}
			
		});
	}
	
	@Test
	public final void testAutoapplyOnce1() {
		BasicsTest.build(new Runnable() {
			
			@Override
			public final void run() {
				Basics.setup();
				
				suppose(newName(), "condition1");
				suppose(newName(), "condition2");
				
				suppose($rule("condition1", "condition2", "conclusion1"));
				
				{
					newGoal("conclusion1");
					
					autoapplyOnce(name(-1));
					autoapplyOnce(name(-1));
					
					concludeGoal();
				}
			}
			
		});
	}
	
	@Test
	public final void testAutoapply1() {
		BasicsTest.build(new Runnable() {
			
			@Override
			public final void run() {
				Basics.setup();
				
				suppose(newName(), "condition1");
				suppose(newName(), "condition2");
				
				suppose($rule("condition1", "condition2", "conclusion1"));
				
				{
					newGoal("conclusion1");
					
					autoapply(name(-1));
					
					concludeGoal();
				}
			}
			
		});
	}
	
}
