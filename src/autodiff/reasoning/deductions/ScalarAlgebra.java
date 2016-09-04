package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.PatternMatching.match;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.tools.Tools.*;

import autodiff.reasoning.expressions.ExpressionRewriter;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.ElementaryVerification;
import autodiff.reasoning.proofs.Substitution;
import autodiff.reasoning.tactics.Auto;
import autodiff.reasoning.tactics.Stack.AbortException;
import autodiff.rules.Predicate;
import autodiff.rules.Rules.Result;
import autodiff.rules.TryRule;
import autodiff.rules.Variable;

import java.util.Map;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-08-31)
 */
public final class ScalarAlgebra {
	
	private ScalarAlgebra() {
		throw new IllegalInstantiationException();
	}
	
	public static final Auto.Simplifier CANONICALIZER = new Simplifier(Simplifier.Mode.DEFINE)
			.add(newElementarySimplificationRule())
			.add(newSubtractionSimplificationRule())
			.add(newAdditionAssociativitySimplificationRule())
			.add(newMultiplicationAssociativitySimplificationRule())
			.add(newAdditionSimplificationRule())
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
		
		for (final Object type : NUMERIC_TYPES) {
			for (final Object operator : array($("^"))) {
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("stability_of_" + operator + "_in_" + type,
						$(FORALL, _x, IN, type,
								$(FORALL, _y, IN, N,
										$($(_x, operator, _y), IN, type))));
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
								$($($(_x, operator, _y), operator, _z), "=", $(_x, operator, $(_y, operator, _z)))));
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
				autobindTrim("stability_of_+_in_" + R, vx.get(), vy.get());
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			hintAutodeduce(tryMatch($($(vx, "-", vy), IN, R), (e, m) -> {
				autobindTrim("stability_of_-_in_" + R, vx.get(), vy.get());
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			hintAutodeduce(tryMatch($($(vx, "*", vy), IN, R), (e, m) -> {
				autobindTrim("stability_of_*_in_" + R, vx.get(), vy.get());
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			hintAutodeduce(tryMatch($($(vx, "/", vy), IN, R), (e, m) -> {
				autobindTrim("stability_of_/_in_" + R, vx.get(), vy.get());
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			hintAutodeduce(tryMatch($($(vx, "^", vy), IN, R), (e, m) -> {
				autobindTrim("stability_of_^_in_" + R, vx.get(), vy.get());
				
				return true;
			}));
		}
	}
	
	public static final TryRule<Object> newIgnoreRule() {
		return (e, m) -> TryRule.F;
	}
	
	public static final TryRule<Object> newElementarySimplificationRule() {
		return tryPredicate((e, m) -> {
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
		});
	}
	
	public static final TryRule<Object> newAdditionSimplificationRule() {
		/*
		 * 
		 * ax+bx -> (a+b)x
		 * ax+x  -> (a+1)x
		 * x+bx  -> (1+b)x
		 * x+x   -> (1+1)x
		 * 
		 * by+ax -> ax+by
		 * y+ax  -> ax+y
		 * by+x  -> x+by
		 * y+x   -> x+y
		 * 
		 */
		return tryPredicate((e, m) -> {
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			final Variable va = new Variable("a");
			final Variable vb = new Variable("b");
			
			final Object vax = $(va, "*", vx);
			final Object vbx = $(vb, "*", vx);
			final Object vby = $(vb, "*", vy);
			
			Boolean result;
			
			result = tryAddition(vx, va, vb, vax, vbx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAddition(vx, va, 1, vax, vx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAddition(vx, 1, vb, vx, vbx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAddition(vx, 1, 1, vx, vx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAddition(vx, vy, va, vb, vax, vby, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAddition(vx, vy, va, 1, vax, vy, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAddition(vx, vy, 1, vb, vx, vby, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAddition(vx, vy, 1, 1, vx, vy, e);
			
			if (result != null) {
				return result;
			}
			
			return false;
		});
	}
	
	public static final Boolean tryAddition(final Object vx,
			final Object va, final Object vb, final Object vax, final Object vbx, final Object expression) {
		if (match($(vax, "+", vbx), expression)) {
			final Object _x = get(vx);
			final Object _a = get(va);
			final Object _b = get(vb);
			
			final boolean vaIs1 = "1".equals(va.toString());
			final boolean vbIs1 = "1".equals(vb.toString());
			
			if (!vaIs1 && !vbIs1) {
				try {
					autobindTrim("simplification_of_a*x+b*x", _x, _a, _b);
					
					return true;
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					ignore(exception);
				}
			} else {
				final Deduction deduction = subdeduction();
				
				try {
					bind("identity", expression);
					
					if (vaIs1 && vbIs1) {
						autobindTrim("neutrality_of_1", _x);
						rewriteRight(name(-2), name(-1), 2, 3);
					} else if (vaIs1) {
						autobindTrim("neutrality_of_1", _x);
						rewriteRight(name(-2), name(-1), 2);
					} else if (vbIs1) {
						autobindTrim("neutrality_of_1", _x);
						rewriteRight(name(-2), name(-1), 3);
					}
					
					autobindTrim("simplification_of_a*x+b*x", _x, _a, _b);
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
		
		return null;
	}
	
	public static final Boolean tryAddition(final Object vx, final Object vy,
			final Object va, final Object vb, final Object vax, final Object vby, final Object expression) {
		if (match($(vby, "+", vax), expression)) {
			final Object _x = get(vx);
			final Object _y = get(vy);
			final Object _a = get(va);
			final Object _b = get(vb);
			final Object _ax = get(vax);
			final Object _by = get(vby);
			
			if (_a instanceof Number && _b instanceof Number) {
				final Object binary = $(new Variable("?"), "+", new Variable("?"));
				
				if (match(binary, _ax) || match(binary, _by)) {
					return null;
				}
				
				if (compare(_x, _y) < 0) {
					try {
						autobindTrim("commutativity_of_+_in_" + R, _by, _ax);
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
					}
				}
				
				return false;
			}
		}
		
		return null;
	}
	
	public static final int compare(final Object object1, final Object object2) {
		final Number n1 = cast(Number.class, object1);
		final Number n2 = cast(Number.class, object2);
		
		if (n1 != null && n2 != null) {
			return 0;
		}
		
		if (n1 != null) {
			return -1;
		}
		
		if (n2 != null) {
			return 1;
		}
		
		return object1.toString().compareTo(object2.toString());
	}
	
	public static final TryRule<Object> newAdditionAssociativitySimplificationRule() {
		/*
		 * 
		 * (x+y)+z   -> x+(y+z)
		 * 
		 * ax+(bx+z) -> (a+b)x+z
		 * ax+(x+z)  -> (a+1)x+z
		 * x+(bx+z)  -> (1+b)x+z
		 * x+(x+z)   -> (1+1)x+z
		 * 
		 * by+(ax+z) -> ax+(by+z)
		 * y+(ax+z)  -> ax+(y+z)
		 * by+(x+z)  -> x+(by+z)
		 * y+(x+z)   -> x+(y+z)
		 * 
		 */
		return tryPredicate((e, m) -> {
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			final Variable vz = new Variable("z");
			final Variable va = new Variable("a");
			final Variable vb = new Variable("b");
			
			final Object vax = $(va, "*", vx);
			final Object vbx = $(vb, "*", vx);
			final Object vby = $(vb, "*", vy);
			
			if (match($($(vx, "+", vy), "+", vz), e)) {
				try {
					autobindTrim("associativity_of_+_+_in_" + R, vx.get(), vy.get(), vz.get());
					
					return true;
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					ignore(exception);
				}
			}
			
			Boolean result;
			
			result = tryAdditionAssociativity(vx, vz, va, vb, vax, vbx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAdditionAssociativity(vx, vz, va, 1, vax, vx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAdditionAssociativity(vx, vz, 1, vb, vx, vbx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAdditionAssociativity(vx, vz, 1, 1, vx, vx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAdditionAssociativity(vx, vy, vz, va, vb, vax, vby, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAdditionAssociativity(vx, vy, vz, va, 1, vax, vy, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAdditionAssociativity(vx, vy, vz, 1, vb, vx, vby, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryAdditionAssociativity(vx, vy, vz, 1, 1, vx, vy, e);
			
			if (result != null) {
				return result;
			}
			
			return false;
		});
	}
	
	public static final Boolean tryAdditionAssociativity(final Object vx, final Object vy, final Object vz,
			final Object va, final Object vb, final Object vax, final Object vby, final Object expression) {
		if (match($(vby, "+", $(vax, "+", vz)), expression)) {
			final Object _x = get(vx);
			final Object _y = get(vy);
			final Object _z = get(vz);
			final Object _a = get(va);
			final Object _b = get(vb);
			final Object _ax = get(vax);
			final Object _by = get(vby);
			
			if (_a instanceof Number && _b instanceof Number) {
				if (compare(_x, _y) < 0) {
					final Deduction deduction = subdeduction();
					
					try {
						bind("identity", expression);
						autobindTrim("associativity_of_+_+_in_" + R, _by, _ax, _z);
						rewriteRight(name(-2), name(-1), 1);
						
						autobindTrim("commutativity_of_+_in_" + R, _by, _ax);
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
				
				return false;
			}
		}
		
		return null;
	}
	
	public static final Boolean tryAdditionAssociativity(final Object vx, final Object vz,
			final Object va, final Object vb, final Object vax, final Object vbx, final Object expression) {
		if (match($(vax, "+", $(vbx, "+", vz)), expression)) {
			final Object _x = get(vx);
			final Object _a = get(va);
			final Object _b = get(vb);
			final Object _ax = get(vax);
			final Object _bx = get(vbx);
			final Object _z = get(vz);
			final Deduction deduction = subdeduction();
			
			try {
				bind("identity", expression);
				autobindTrim("associativity_of_+_+_in_" + R, _ax, _bx, _z);
				rewriteRight(name(-2), name(-1), 1);
				
				final boolean vaIs1 = "1".equals(va.toString());
				final boolean vbIs1 = "1".equals(vb.toString());
				
				if (vaIs1 && vbIs1) {
					autobindTrim("neutrality_of_1", _x);
					rewriteRight(name(-2), name(-1), 2, 3);
				} else if (vaIs1) {
					autobindTrim("neutrality_of_1", _x);
					rewriteRight(name(-2), name(-1), 2);
				} else if (vbIs1) {
					autobindTrim("neutrality_of_1", _x);
					rewriteRight(name(-2), name(-1), 3);
				}
				
				autobindTrim("simplification_of_a*x+b*x", _x, _a, _b);
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
		
		return null;
	}
	
	public static final Object get(final Object pattern) {
		return new ExpressionRewriter() {
			
			@Override
			public final Object visit(final Object expression) {
				final Variable v = cast(Variable.class, expression);
				
				return v != null ? v.get() : ExpressionRewriter.super.visit(expression);
			}
			
			private static final long serialVersionUID = -680915770150424735L;
			
		}.apply(pattern);
	}
	
	public static final TryRule<Object> newMultiplicationAssociativitySimplificationRule() {
		/*
		 * 
		 * (x*y)*z     -> x*(y*z)
		 * 
		 * x^a*(x^b*z) -> x^(a+b)*z
		 * x^a*(x*z)   -> x^(a+1)*z
		 * x*(x^b*z)   -> x^(1+b)*z
		 * x*(x*z)     -> x^(1+1)*z
		 * 
		 * y*(x*z)     -> x*(y*z)
		 * 
		 */
		return tryPredicate((e, m) -> {
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			final Variable vz = new Variable("z");
			final Variable va = new Variable("a");
			final Variable vb = new Variable("b");
			
			final Object vxa = $(vx, "^", va);
			final Object vxb = $(vx, "^", vb);
			
			if (match($($(vx, "*", vy), "*", vz), e)) {
				try {
					autobindTrim("associativity_of_*_*_in_" + R, vx.get(), vy.get(), vz.get());
					
					return true;
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					ignore(exception);
				}
			}
			
			Boolean result;
			
			result = tryMultiplicationAssociativity(vx, vz, va, vb, vxa, vxb, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryMultiplicationAssociativity(vx, vz, va, 1, vxa, vx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryMultiplicationAssociativity(vx, vz, 1, vb, vx, vxb, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryMultiplicationAssociativity(vx, vz, 1, 1, vx, vx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryMultiplicationAssociativity(vx, vy, vz, 1, 1, vx, vy, e);
			
			if (result != null) {
				return result;
			}
			
			return false;
		});
	}
	
	public static final Boolean tryMultiplicationAssociativity(final Object vx, final Object vz,
			final Object va, final Object vb, final Object vxa, final Object vxb, final Object expression) {
		if (match($(vxa, "*", $(vxb, "*", vz)), expression)) {
			final Object _x = get(vx);
			final Object _a = get(va);
			final Object _b = get(vb);
			final Object _xa = get(vxa);
			final Object _xb = get(vxb);
			final Object _z = get(vz);
			final Deduction deduction = subdeduction();
			
			try {
				bind("identity", expression);
				autobindTrim("associativity_of_*_*_in_" + R, _xa, _xb, _z);
				rewriteRight(name(-2), name(-1), 1);
				
				final boolean vaIs1 = "1".equals(va.toString());
				final boolean vbIs1 = "1".equals(vb.toString());
				
				if (vaIs1 && vbIs1) {
					autobindTrim("definition_of_x^1", _x);
					rewriteRight(name(-2), name(-1), 2, 3);
				} else if (vaIs1) {
					autobindTrim("definition_of_x^1", _x);
					rewriteRight(name(-2), name(-1), 2);
				} else if (vbIs1) {
					autobindTrim("definition_of_x^1", _x);
					rewriteRight(name(-2), name(-1), 3);
				}
				
				autobindTrim("simplification_of_x^a*x^b", _x, _a, _b);
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
		
		return null;
	}
	
	public static final Boolean tryMultiplicationAssociativity(final Object vx, final Object vy, final Object vz,
			final Object va, final Object vb, final Object vxa, final Object vyb, final Object expression) {
		if (match($(vyb, "*", $(vxa, "*", vz)), expression)) {
			final Object _x = get(vx);
			final Object _y = get(vy);
			final Object _z = get(vz);
			final Object _a = get(va);
			final Object _b = get(vb);
			final Object _xa = get(vxa);
			final Object _yb = get(vyb);
			
			if (_a instanceof Number && _b instanceof Number) {
				if (compare(_x, _y) < 0) {
					final Deduction deduction = subdeduction();
					
					try {
						bind("identity", expression);
						autobindTrim("associativity_of_*_*_in_" + R, _yb, _xa, _z);
						rewriteRight(name(-2), name(-1), 1);
						
						autobindTrim("commutativity_of_*_in_" + R, _yb, _xa);
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
				
				return false;
			}
		}
		
		return null;
	}
	
	public static final TryRule<Object> newSubtractionSimplificationRule() {
		return tryPredicate((e, m) -> {
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			if (match($(vx, "-", vy), e)) {
				final Object _x = vx.get();
				final Object _y = vy.get();
				
				autobindTrim("definition_of_-_in_" + R, _x, _y);
				
				return true;
			}
			
			return false;
		});
	}
	
	public static final <T> TryRule<T> tryPredicate(final Predicate<T> predicate) {
		return new TryRule<T>() {
			
			@Override
			public final Result<Boolean> apply(final T t, final Map<Variable, Object> u) {
				if (predicate.test(t, u)) {
					return T;
				}
				
				return null;
			}
			
			private static final long serialVersionUID = 2615332966395330391L;
			
		};
	}
	
	public static final TryRule<Object> newMultiplicationSimplificationRule() {
		/*
		 * 
		 * x^a*x^b -> x^(a+b)
		 * x^a*x   -> x^(a+1)
		 * x*x^b   -> x^(1+b)
		 * x*x     -> x^(1+1)
		 * 
		 * y*x     -> x*y
		 * 
		 */
		return tryPredicate((e, m) -> {
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			final Variable va = new Variable("a");
			final Variable vb = new Variable("b");
			
			final Object vxa = $(vx, "^", va);
			final Object vxb = $(vx, "^", vb);
			
			Boolean result;
			
			result = tryMultiplication(vx, va, vb, vxa, vxb, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryMultiplication(vx, va, 1, vxa, vx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryMultiplication(vx, 1, vb, vx, vxb, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryMultiplication(vx, 1, 1, vx, vx, e);
			
			if (result != null) {
				return result;
			}
			
			result = tryMultiplication(vx, vy, 1, 1, vx, vy, e);
			
			if (result != null) {
				return result;
			}
			
			return false;
		});
	}
	
	public static final Boolean tryMultiplication(final Object vx,
			final Object va, final Object vb, final Object vax, final Object vbx, final Object expression) {
		if (match($(vax, "*", vbx), expression)) {
			final Object _x = get(vx);
			final Object _a = get(va);
			final Object _b = get(vb);
			
			final boolean vaIs1 = "1".equals(va.toString());
			final boolean vbIs1 = "1".equals(vb.toString());
			
			if (!vaIs1 && !vbIs1) {
				try {
					autobindTrim("simplification_of_x^a*x^b", _x, _a, _b);
					
					return true;
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					ignore(exception);
				}
			} else {
				final Deduction deduction = subdeduction();
				
				try {
					bind("identity", expression);
					
					if (vaIs1 && vbIs1) {
						autobindTrim("definition_of_x^1", _x);
						rewriteRight(name(-2), name(-1), 2, 3);
					} else if (vaIs1) {
						autobindTrim("definition_of_x^1", _x);
						rewriteRight(name(-2), name(-1), 2);
					} else if (vbIs1) {
						autobindTrim("definition_of_x^1", _x);
						rewriteRight(name(-2), name(-1), 3);
					}
					
					autobindTrim("simplification_of_x^a*x^b", _x, _a, _b);
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
		
		return null;
	}
	
	public static final Boolean tryMultiplication(final Object vx, final Object vy,
			final Object va, final Object vb, final Object vax, final Object vby, final Object expression) {
		if (match($(vby, "*", vax), expression)) {
			final Object _x = get(vx);
			final Object _y = get(vy);
			final Object _a = get(va);
			final Object _b = get(vb);
			final Object _ax = get(vax);
			final Object _by = get(vby);
			
			if (_a instanceof Number && _b instanceof Number) {
				final Object binary = $(new Variable("?"), "*", new Variable("?"));
				
				if (match(binary, _ax) || match(binary, _by)) {
					return null;
				}
				
				if (compare(_x, _y) < 0) {
					try {
						autobindTrim("commutativity_of_*_in_" + R, _by, _ax);
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
					}
				}
				
				return false;
			}
		}
		
		return null;
	}
	
}
