package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.rewrite;
import static autodiff.reasoning.deductions.Basics.rewriteRight;
import static autodiff.reasoning.deductions.Cases.cases;
import static autodiff.reasoning.deductions.Cases.simplifyCasesInLast;
import static autodiff.reasoning.deductions.Sets.SUBSET;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.PatternMatching.matchOrFail;
import static autodiff.reasoning.tactics.Stack.*;

import multij.rules.Variable;
import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-09-11)
 */
public final class ScalarFunctions {
	
	private ScalarFunctions() {
		throw new IllegalInstantiationException();
	}
	
	private static final Object B = $(N, "_", $("<", 2));
	
	public static final void load() {
		if (!setMetadatumOnce(ScalarFunctions.class, "loaded")) {
			return;
		}
		
		ScalarAlgebra.load();
		Functions.load();
		Cases.load();
		
		/*
		 * XXX
		 * 
		 * Type constraints make it difficult to generate code
		 * because generated code needs to be evaluated in order
		 * to check its type.
		 * 
		 * To keep the type constraints, specific conversion rules
		 * could be added but then genericity would be lost...
		 * 
		 * Universal quantification doesn't feel entirely satisfying
		 * but at least it doesn't prevent typing when required, eg
		 * step_0 : R -> R
		 * 
		 */
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_heaviside_function",
					$forall(_x,
							$($("step_0", _x), "=", cases(
									$(1, "if", $(0, LE, _x)),
									$(0, "otherwise")))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_step_1",
					$forall(_x,
							$($("step_1", _x), "=", cases(
									$(1, "if", $(0, "<", _x)),
									$(0, "otherwise")))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			
			suppose("definition_of_kronecker_function",
					$forall(_x, _y,
							$($("delta_", $(_x, "", _y)), "=", cases(
									$(1, "if", $(_x, "=", _y)),
									$(0, "otherwise")))));
		}
		
		{
			subdeduction("type_of_step_0");
			
			final Object _x = forall("x");
			
			bind("definition_of_heaviside_function", _x);
			
			final Variable vcx = v("cx");
			final Variable vcc = v("cc");
			final Variable vcy = v("cy");
			
			matchOrFail(cases($(vcx, "if", vcc), $(vcy, "otherwise")), right(proposition(-1)));
			
			autobindTrim("type_of_cases_0", B, vcx.get(), vcy.get(), vcc.get());
			
			rewriteRight(name(-1), name(-2));
			
			conclude();
		}
		
		{
			subdeduction("type_of_step_1");
			
			final Object _x = forall("x");
			
			bind("definition_of_step_1", _x);
			
			final Variable vcx = v("cx");
			final Variable vcc = v("cc");
			final Variable vcy = v("cy");
			
			matchOrFail(cases($(vcx, "if", vcc), $(vcy, "otherwise")), right(proposition(-1)));
			
			autobindTrim("type_of_cases_0", B, vcx.get(), vcy.get(), vcc.get());
			
			rewriteRight(name(-1), name(-2));
			
			conclude();
		}
		
		{
			subdeduction("type_of_kronecker");
			
			final Object _x = forall("x");
			final Object _y = forall("y");
			
			bind("definition_of_kronecker_function", _x, _y);
			
			final Variable vcx = v("cx");
			final Variable vcc = v("cc");
			final Variable vcy = v("cy");
			
			matchOrFail(cases($(vcx, "if", vcc), $(vcy, "otherwise")), right(proposition(-1)));
			
			autobindTrim("type_of_cases_0", B, vcx.get(), vcy.get(), vcc.get());
			
			rewriteRight(name(-1), name(-2));
			
			conclude();
		}
		
		{
			subdeduction("range_2_subset_naturals");
			
			autodeduce($(B, SUBSET, N));
			
			conclude();
		}
		
		loadAutoHints();
	}
	
	public static final void loadAutoHints() {
		{
			final Variable vx = v("x");
			final Variable vX = v("X");
			
			hintAutodeduce(tryMatch($($("step_1", vx), IN, vX), (e, m) -> {
				final Object _x = vx.get();
				final Object _X = vX.get();
				
				{
					subdeduction();
					
					autodeduce($(B, SUBSET, _X));
					autobindTrim("definition_of_subset", B, _X);
					rewrite(name(-2), name(-1));
					bind("type_of_step_1", _x);
					autobindTrim(name(-2), left(proposition(-1)));
					
					conclude();
				}
				
				return true;
			}));
		}
		
		{
			final Variable vx = v("x");
			final Variable vy = v("y");
			final Variable vX = v("X");
			
			hintAutodeduce(tryMatch($($("delta_", $(vx, "", vy)), IN, vX), (e, m) -> {
				final Object _x = vx.get();
				final Object _y = vy.get();
				final Object _X = vX.get();
				
				{
					subdeduction();
					
					autodeduce($(B, SUBSET, _X));
					autobindTrim("definition_of_subset", B, _X);
					rewrite(name(-2), name(-1));
					bind("type_of_kronecker", _x, _y);
					autobindTrim(name(-2), left(proposition(-1)));
					
					conclude();
				}
				
				return true;
			}));
		}
	}
	
}
