package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.PatternMatching.match;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.tools.Tools.array;
import static multij.tools.Tools.ignore;

import java.util.Map;

import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.ElementaryVerification;
import autodiff.reasoning.proofs.Substitution;
import autodiff.reasoning.tactics.Auto;
import autodiff.reasoning.tactics.Stack.AbortException;
import autodiff.rules.SimpleRule;
import autodiff.rules.TryRule;
import autodiff.rules.Variable;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-08-31)
 */
public final class ScalarAlgebra {
	
	private ScalarAlgebra() {
		throw new IllegalInstantiationException();
	}
	
	public static final Auto.Simplifier CANONICALIZER = new Simplifier(Simplifier.Mode.DEFINE)
			.add(newElementarySimplificationRule2())
			.add(newAdditionSimplificationRule())
			.add(newSubtractionSimplificationRule())
			.add(newMultiplicationSimplificationRule())
			.add(newIgnoreRule());
	
	public static final Object[] NUMERIC_TYPES = { N, Z, Q, R };
	
	public static final Object[] RELATIVE_TYPES = { Z, Q, R };
	
	public static final Object[] RATIONAL_TYPES = { Q, R };
	
	public static final void load() {
		Sets.load();
		
		for (final Object type : NUMERIC_TYPES) {
			for (final Object operator : array($("+"), $("*"))) {
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("stability_of_" + operator + "_in_" + type,
						$(FORALL, _x, ",", _y, IN, type,
								$($(_x, operator, _y), IN, type)));
			}
		}
		
		for (final Object type : RELATIVE_TYPES) {
			for (final Object operator : array($("-"))) {
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("stability_of_" + operator + "_in_" + type,
						$(FORALL, _x, ",", _y, IN, type,
								$($(_x, operator, _y), IN, type)));
			}
		}
		
		for (final Object type : RATIONAL_TYPES) {
			for (final Object operator : array($("/"))) {
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("stability_of_" + operator + "_in_" + type,
						$(FORALL, _x, ",", _y, IN, type,
								$rule(notZero(_y), $($(_x, operator, _y), IN, type))));
			}
		}
		
		for (final Object type : array(Z)) {
			for (final Object operator : array($("/"))) {
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("stability_of_" + operator + "_in_" + type,
						$(FORALL, _x, ",", _y, IN, type,
								$rule($($(_x, "%", _y), "=", 0), $($(_x, operator, _y), IN, type))));
			}
		}
		
		for (final Object operator : array($("+"), $("*"))) {
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("commutativity_of_" + operator + "_in_" + R,
						$(FORALL, _x, ",", _y, IN, R,
								$($(_x, operator, _y), "=", $(_y, operator, _x))));
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _z = $new("z");
				
				suppose("associativity_of_" + operator + "_" + operator + "_in_" + R,
						$(FORALL, _x, ",", _y, ",", _z, IN, R,
								$($(_x, operator, $(_y, operator, _z)), "=", $($(_x, operator, _y), operator, _z))));
			}
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			
			suppose("definition_of_-_in_" + R,
					$(FORALL, _x, ",", _y, IN, R,
							$($(_x, "-", _y), "=", $(_x, "+", $(-1, "*", _y)))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			
			suppose("definition_of_/_in_" + R,
					$(FORALL, _x, ",", _y, IN, R,
							$rule(notZero(_y), $($(_x, "/", _y), "=", $(_x, "*", $(_y, "^", -1))))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("conversion_from_" + Z + "_to_" + N,
					$(FORALL, _x, IN, Z,
							$rule($(0, LE, _x), $(_x, IN, N))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_x^0",
					$(FORALL, _x, IN, R,
							$($(_x, "^", 0), "=", 1)));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("definition_of_x^1",
					$(FORALL, _x, IN, R,
							$($(_x, "^", 1), "=", _x)));
		}
		
		{
			final Object _x = $new("x");
			final Object _a = $new("a");
			final Object _b = $new("b");
			
			suppose("simplification_of_nonzero_x^a*x^b",
					$(FORALL, _x, IN, R,
							$(FORALL, _a, ",", _b, IN, Z,
									$rule(notZero(_x), $($(_x, "^", _a), "*", $(_x, "^", _b)), "=", $(_x, "^", $(_a, "+", _b))))));
		}
		
		{
			final Object _x = $new("x");
			final Object _a = $new("a");
			final Object _b = $new("b");
			
			suppose("simplification_of_x^a*x^b",
					$(FORALL, _x, IN, R,
							$(FORALL, _a, ",", _b, IN, N,
									$($($(_x, "^", _a), "*", $(_x, "^", _b)), "=", $(_x, "^", $(_a, "+", _b))))));
		}
		
		{
			final Object _x = $new("x");
			final Object _a = $new("a");
			final Object _b = $new("b");
			
			suppose("simplification_of_nonzero_x^a^b",
					$(FORALL, _x, IN, R,
							$(FORALL, _a, ",", _b, IN, Z,
									$rule(notZero(_x), $($($(_x, "^", _a), "^", _b), "=", $(_x, "^", $(_a, "*", _b)))))));
		}
		
		{
			final Object _x = $new("x");
			final Object _a = $new("a");
			final Object _b = $new("b");
			
			suppose("simplification_of_x^a^b",
					$(FORALL, _x, IN, R,
							$(FORALL, _a, ",", _b, IN, N,
									$($($(_x, "^", _a), "^", _b), "=", $(_x, "^", $(_a, "*", _b))))));
		}
		
		{
			final Object _x = $new("x");
			final Object _a = $new("a");
			final Object _b = $new("b");
			
			suppose("simplification_of_a*x+b*x",
					$(FORALL, _x, ",", _a, ",", _b, IN, R,
							$($($(_a, "*", _x), "+", $(_b, "*", _x)), "=", $($(_a, "+", _b), "*", _x))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("neutrality_of_0",
					$(FORALL, _x, IN, R,
							$($(_x, "+", 0), "=", _x)));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("neutrality_of_1",
					$(FORALL, _x, IN, R,
							$($(1, "*", _x), "=", _x)));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("absorbingness_of_0",
					$(FORALL, _x, IN, R,
							$($(0, "*", _x), "=", 0)));
		}
		
		loadAutoHints();
	}
	
	public static final void canonicalize(final Object expression) {
		canonicalize(newName(), expression);
	}
	
	public static final void canonicalize(final String propositionName, final Object expression) {
		subdeduction(propositionName);
		
		bind("identity", expression);
		CANONICALIZER.simplifyCompletely(proposition(-1));
		
		conclude();
	}
	
	public static final Object notZero(final Object _x) {
		return $(LNOT, $(_x, "=", 0));
	}
	
	public static final void loadAutoHints() {
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			hintAutodeduce(tryMatch($($(vx, "+", vy), IN, R), (e, m) -> {
				subdeduction();
				
				autobind("stability_of_+_in_" + R, vx.get(), vy.get());
				autoapply(name(-1));
				
				conclude();
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			hintAutodeduce(tryMatch($($(vx, "-", vy), IN, R), (e, m) -> {
				subdeduction();
				
				autobind("stability_of_-_in_" + R, vx.get(), vy.get());
				autoapply(name(-1));
				
				conclude();
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			hintAutodeduce(tryMatch($($(vx, "*", vy), IN, R), (e, m) -> {
				subdeduction();
				
				autobind("stability_of_*_in_" + R, vx.get(), vy.get());
				autoapply(name(-1));
				
				conclude();
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			hintAutodeduce(tryMatch($($(vx, "/", vy), IN, R), (e, m) -> {
				subdeduction();
				
				autobind("stability_of_/_in_" + R, vx.get(), vy.get());
				autoapply(name(-1));
				
				conclude();
				
				return true;
			}));
		}
	}
	
	public static final SimpleRule<Object, Boolean> newElementarySimplificationRule() {
		return new SimpleRule<>((e, m) -> {
			try {
				final Object f = ElementaryVerification.Evaluator.INSTANCE.apply(e);
				
				return !f.equals(e) && !Substitution.deepContains(f, null);
			} catch (final AbortException exception) {
				throw exception;
			} catch (final Exception exception) {
				ignore(exception);
			}
			
			return false;
		}, (e, m) -> {
			try {
				final Object f = ElementaryVerification.Evaluator.INSTANCE.apply(e);
				
				verifyElementaryProposition($(e, "=", f));
				
				return true;
			} catch (final AbortException exception) {
				throw exception;
			} catch (final Exception exception) {
				ignore(exception);
			}
			
			return false;
		});
	}
	
	public static final TryRule<Object> newIgnoreRule() {
		return new TryRule<Object>() {
			
			@Override
			public final boolean test(final Object object, final Map<Variable, Object> mapping) {
				return true;
			}
			
			@Override
			public final Boolean applyTo(final Object object, final Map<Variable, Object> mapping) {
				return false;
			}
			
			private static final long serialVersionUID = 5917717573706684334L;
			
		};
	}
	
	public static final TryRule<Object> newElementarySimplificationRule2() {
		return (e, m) -> {
			try {
				final Object f = ElementaryVerification.Evaluator.INSTANCE.apply(e);
				
				if (!f.equals(e) && !Substitution.deepContains(f, null)) {
					verifyElementaryProposition($(e, "=", f));
					
					return true;
				}
			} catch (final AbortException exception) {
				throw exception;
			} catch (final Exception exception) {
				ignore(exception);
			}
			
			return false;
		};
	}
	
	public static final TryRule<Object> newAdditionSimplificationRule() {
		return (e, m) -> {
			final Variable vx = new Variable("x");
			final Variable va = new Variable("a");
			final Variable vb = new Variable("b");
			
			if (match($($(va, "*", vx), "+", $(vb, "*", vx)), e)) {
				final Object _x = vx.get();
				final Object _a = va.get();
				final Object _b = vb.get();
				
				if (_a instanceof Number && _b instanceof Number) {
					try {
						autobindTrim("simplification_of_a*x+b*x", _x, _a, _b);
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
					}
				}
			}
			
			if (match($(vx, "+", $(vb, "*", vx)), e)) {
				final Object _x = vx.get();
				final Object _b = vb.get();
				final Deduction deduction = subdeduction();
				
				if (_b instanceof Number) {
					try {
						bind("identity", e);
						autobindTrim("neutrality_of_1", _x);
						rewriteRight(name(-2), name(-1), 2);
						
						autobindTrim("simplification_of_a*x+b*x", _x, 1, _b);
						rewrite(name(-2), name(-1));
						
						conclude();
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
						
						popTo(deduction.getParent());
					}
				}
			}
			
			if (match($($(va, "*", vx), "+", vx), e)) {
				final Object _x = vx.get();
				final Object _a = va.get();
				final Deduction deduction = subdeduction();
				
				if (_a instanceof Number) {
					try {
						bind("identity", e);
						autobindTrim("neutrality_of_1", _x);
						rewriteRight(name(-2), name(-1), 3);
						
						autobindTrim("simplification_of_a*x+b*x", _x, _a, 1);
						rewrite(name(-2), name(-1));
						
						conclude();
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
						
						popTo(deduction.getParent());
					}
				}
			}
			
			if (match($(0, "+", vx), e)) {
				final Object _x = vx.get();
				final Deduction deduction = subdeduction();
				
				try {
					autobindTrim("commutativity_of_+_in_" + R, 0, _x);
					autobindTrim("neutrality_of_0", _x);
					rewrite(name(-2), name(-1));
					
					conclude();
					
					return true;
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					ignore(exception);
					
					popTo(deduction.getParent());
				}
			}
			
			if (match($(vx, "+", vx), e)) {
				final Object _x = vx.get();
				final Deduction deduction = subdeduction();
				
				try {
					bind("identity", e);
					autobindTrim("neutrality_of_1", _x);
					rewriteRight(name(-2), name(-1), 2, 3);
					
					autobindTrim("simplification_of_a*x+b*x", _x, 1, 1);
					rewrite(name(-2), name(-1));
					
					conclude();
					
					return true;
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					ignore(exception);
					
					popTo(deduction.getParent());
				}
			}
			
			if (match($(vb, "+", va), e)) {
				final Object _a = va.get();
				final Object _b = vb.get();
				
				if (_a.toString().compareTo(_b.toString()) < 0) {
					try {
						autobindTrim("commutativity_of_+_in_" + R, _b, _a);
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
					}
				}
			}
			
			return false;
		};
	}
	
	public static final TryRule<Object> newSubtractionSimplificationRule() {
		return (e, m) -> {
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			if (match($(vx, "-", vy), e)) {
				final Object _x = vx.get();
				final Object _y = vy.get();
				
				autobindTrim("definition_of_-_in_" + R, _x, _y);
				
				return true;
			}
			
			return false;
		};
	}
	
	public static final TryRule<Object> newMultiplicationSimplificationRule() {
		return (e, m) -> {
			final Variable vx = new Variable("x");
			final Variable va = new Variable("a");
			final Variable vb = new Variable("b");
			
			if (match($($(vx, "^", va), "*", $(vx, "^", vb)), e)) {
				final Object _x = vx.get();
				final Object _a = va.get();
				final Object _b = vb.get();
				
				if (_a instanceof Number && _b instanceof Number) {
					try {
						autobindTrim("simplification_of_x^a*x^b", _x, _a, _b);
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
					}
				}
			}
			
			if (match($(vx, "*", $(vx, "^", vb)), e)) {
				final Object _x = vx.get();
				final Object _b = vb.get();
				final Deduction deduction = subdeduction();
				
				if (_b instanceof Number) {
					try {
						bind("identity", e);
						autobindTrim("definition_of_x^1", _x);
						rewriteRight(name(-2), name(-1), 2);
						
						autobindTrim("simplification_of_x^a*x^b", _x, 1, _b);
						rewrite(name(-2), name(-1));
						
						conclude();
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
						
						popTo(deduction.getParent());
					}
				}
			}
			
			if (match($($(va, "*", vx), "+", vx), e)) {
				final Object _x = vx.get();
				final Object _a = va.get();
				final Deduction deduction = subdeduction();
				
				if (_a instanceof Number) {
					try {
						bind("identity", e);
						autobindTrim("definition_of_x^1", _x);
						rewriteRight(name(-2), name(-1), 3);
						
						autobindTrim("simplification_of_x^a*x^b", _x, _a, 1);
						rewrite(name(-2), name(-1));
						
						conclude();
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
						
						popTo(deduction.getParent());
					}
				}
			}
			
			if (match($(0, "*", vx), e)) {
				final Object _x = vx.get();
				
				try {
					autobindTrim("absorbingness_of_0", _x);
					
					return true;
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					ignore(exception);
				}
			}
			
			if (match($(1, "*", vx), e)) {
				final Object _x = vx.get();
				
				try {
					autobindTrim("neutrality_of_1", _x);
					
					return true;
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					ignore(exception);
				}
			}
			
			if (match($(vx, "*", vx), e)) {
				final Object _x = vx.get();
				final Deduction deduction = subdeduction();
				
				try {
					bind("identity", e);
					autobindTrim("definition_of_x^1", _x);
					rewriteRight(name(-2), name(-1), 2, 3);
					
					autobindTrim("simplification_of_x^a*x^b", _x, 1, 1);
					rewrite(name(-2), name(-1));
					
					conclude();
					
					return true;
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					ignore(exception);
					
					popTo(deduction.getParent());
				}
			}
			
			if (match($(vb, "*", va), e)) {
				final Object _a = va.get();
				final Object _b = vb.get();
				
				if (_a.toString().compareTo(_b.toString()) < 0) {
					try {
						autobindTrim("commutativity_of_*_in_" + R, _b, _a);
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
					}
				}
			}
			
			return false;
		};
	}
	
}
