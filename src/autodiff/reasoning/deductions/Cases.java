package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.rewrite;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.PatternMatching.matchOrFail;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.tools.Tools.*;

import autodiff.reasoning.tactics.Auto.Simplifier;
import autodiff.reasoning.tactics.Auto.Simplifier.Mode;

import multij.rules.Variable;
import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-08-28)
 */
public final class Cases {
	
	private Cases() {
		throw new IllegalInstantiationException();
	}
	
	public static final void load() {
		if (!setMetadatumOnce(Cases.class, "loaded")) {
			return;
		}
		
		supposeEliminationsOfCases();
		testEliminationOfCases();
	}
	
	public static final void supposeEliminationsOfCases() {
		{
			final Object _x = $new("x");
			
			suppose("try_cases_otherwise",
					$forall(_x,
							$(cases($(_x, "otherwise")), "=", _x)));
		}
		
		{
			final Object _x = $new("x");
			final Object _c = $new("c");
			
			suppose("try_cases_if",
					$forall(_x, _c,
							$rule(_c, $(cases($(_x, "if", _c)), "=", _x))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			final Object _c = $new("c");
			
			suppose("try_cases_if_stop",
					$forall(_x, _y, _c,
							$rule(_c,
									$($("cases", $("", $(_x, "if", _c), _y)), "=", _x))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			final Object _c = $new("c");
			
			suppose("try_cases_if_not",
					$forall(_x, _y, _c,
							$rule($(LNOT, _c),
									$($("cases", $("", $(_x, "if", _c), _y)), "=", $("cases", _y)))));
		}
	}

	public static final void testEliminationOfCases() {
		{
			subdeduction("try_cases.test1");
			
			final Object _x = forall("x");
			
			suppose($(_x, "=", cases(
					$(42, "if", $(2, "=", 2)),
					$(24, "otherwise"))));
			
			{
				subdeduction();
				
				bind("try_cases_if_stop", 42, $("", $(24, "otherwise")), $(2, "=", 2));
				verifyElementaryProposition($(2, "=", 2));
				apply(name(-2), name(-1));
				
				conclude();
			}
			
			rewrite(name(-2), name(-1));
			
			conclude();
		}
		
		{
			subdeduction("try_cases.test2");
			
			final Object _x = forall("x");
			
			suppose($(_x, "=", cases(
					$(42, "if", $(2, "=", 3)),
					$(24, "if", $(1, "=", 2)),
					$(0, "otherwise"))));
			
			{
				subdeduction();
				
				{
					subdeduction();
					
					bind("try_cases_if_not", 42, $("", $(24, "if", $(1, "=", 2)), $("", $(0, "otherwise"))), $(2, "=", 3));
					verifyElementaryProposition($(2, "=", 3));
					apply(name(-2), name(-1));
					
					conclude();
				}
				
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			{
				subdeduction();
				
				{
					subdeduction();
					
					bind("try_cases_if_not", 24, $("", $(0, "otherwise")), $(1, "=", 2));
					verifyElementaryProposition($(1, "=", 2));
					apply(name(-2), name(-1));
					
					conclude();
				}
				
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			{
				subdeduction();
				
				{
					subdeduction();
					
					bind("try_cases_otherwise", 0);
					
					conclude();
				}
				
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			conclude();
		}
	}
	
	public static final Object cases(final Object... cases) {
		return Sequences.sequence("", append(array((Object) "cases"), cases));
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
