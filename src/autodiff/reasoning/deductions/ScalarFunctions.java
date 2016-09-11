package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Cases.cases;
import static autodiff.reasoning.deductions.Cases.simplifyCasesInLast;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.R;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.Stack.*;
import static autodiff.reasoning.tactics.Stack.PropositionDescription.potentialJustificationsFor;
import static multij.tools.Tools.debugPrint;

import java.util.List;

import autodiff.reasoning.tactics.Auto;
import autodiff.reasoning.tactics.PatternMatching;
import autodiff.reasoning.tactics.Stack.PropositionDescription;
import multij.rules.Variable;
import multij.tools.IllegalInstantiationException;
import multij.tools.Pair;
import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-09-11)
 */
public final class ScalarFunctions {
	
	private ScalarFunctions() {
		throw new IllegalInstantiationException();
	}
	
	public static final void load() {
		if (!setMetadatumOnce(ScalarFunctions.class, "loaded")) {
			return;
		}
		
		ScalarAlgebra.load();
		Functions.load();
		Cases.load();
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_heaviside_function",
					$(FORALL, _x, IN, R,
							$($("step_0", _x), "=", cases(
									$(1, "if", $(0, LE, _x)),
									$(0, "otherwise")))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_step_1",
					$(FORALL, _x, IN, R,
							$($("step_1", _x), "=", cases(
									$(1, "if", $(0, "<", _x)),
									$(0, "otherwise")))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			
			suppose("definition_of_kronecker_function",
					$(FORALL, _x, ",", _y, IN, R,
							$($("delta_", $(_x, "", _y)), "=", cases(
									$(1, "if", $(_x, "=", _y)),
									$(0, "otherwise")))));
		}
		
		loadAutoHints();
	}
	
	public static final void loadAutoHints() {
		{
			final Variable vx = v("x");
			final Variable vX = v("X");
			
			hintAutodeduce(tryMatch($($("step_1", vx), IN, vX), (e, m) -> {
				autobindTrim("definition_of_step_1", vx.get());
				simplifyCasesInLast();
//				abort();
				
				return false;
			}));
		}
	}
	
}
