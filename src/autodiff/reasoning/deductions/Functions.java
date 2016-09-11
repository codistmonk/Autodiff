package autodiff.reasoning.deductions;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.Stack.setMetadatumOnce;
import static autodiff.reasoning.tactics.Stack.suppose;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-09-11)
 */
public final class Functions {
	
	private Functions() {
		throw new IllegalInstantiationException();
	}
	
	public static final void load() {
		if (!setMetadatumOnce(Functions.class, "loaded")) {
			return;
		}
		
		Sets.load();
		
		{
			final Object _f = $new("f");
			final Object _x = $new("x");
			final Object _X = $new("X");
			final Object _Y = $new("Y");
			
			suppose("definition_of_function_type",
					$forall(_f, _X, _Y,
							$(FORALL, _x, IN, _X,
									$($($(_f, _x), IN, _Y),
											"=", $(_f, ":", _X, "→", _Y)))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			final Object _X = $new("X");
			final Object _Y = $new("Y");
			
			suppose("definition_of_anonymous_function",
					$forall(_X, _Y,
							$(FORALL, _x, IN, _X,
									$(FORALL, _y, IN, _Y,
											$($(_x, "↦", _y), ":", _X, "→", _Y)))));
		}
	}
	
}
