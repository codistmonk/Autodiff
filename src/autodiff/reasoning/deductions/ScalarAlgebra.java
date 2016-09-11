package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.deductions.Sets.SUBSET;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.tactics.Auto.*;
import static autodiff.reasoning.tactics.PatternMatching.match;
import static autodiff.reasoning.tactics.Stack.*;
import static autodiff.reasoning.tactics.Stack.PropositionDescription.existingJustificationFor;
import static autodiff.reasoning.tactics.Stack.PropositionDescription.potentialJustificationsFor;
import static multij.tools.Tools.*;

import autodiff.reasoning.expressions.ExpressionRewriter;
import autodiff.reasoning.expressions.ExpressionVisitor;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.ElementaryVerification;
import autodiff.reasoning.proofs.Substitution;
import autodiff.reasoning.tactics.Auto;
import autodiff.reasoning.tactics.PatternMatching;
import autodiff.reasoning.tactics.Stack.AbortException;
import autodiff.reasoning.tactics.Stack.PropositionDescription;
import multij.rules.Predicate;
import multij.rules.Rules.Result;
import multij.rules.TryRule;
import multij.rules.Variable;

import java.io.Serializable;
import java.math.BigDecimal;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import multij.tools.IllegalInstantiationException;
import multij.tools.Pair;

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
		if (!setMetadatumOnce(ScalarAlgebra.class, "loaded")) {
			return;
		}
		
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
							$($(0, "+", _x), "=", _x)));
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
		
		{
			final Object _x = $new("x");
			
			suppose("nonnegativity_of_naturals",
					$(FORALL, _x, IN, N,
							$(0, LE, _x)));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			final Object _z = $new("z");
			
			suppose("distributivity_of_*_over_+",
					$(FORALL, _x, ",", _y, ",", _z, IN, R,
							$($(_x, "*", $(_y, "+", _z)), "=", $($(_x, "*", _y), "+", $(_x, "*", _z)))));
		}
		
		for (final Object operator : array($("<"), $("<="), LE, ">", ">=", GE)) {
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _z = $new("z");
				
				suppose("transitivity_of_" + operator,
						$(FORALL, _x, ",", _y, ",", _z, IN, R,
								$rule($(_x, operator, _y), $(_y, operator, _z), $(_x, operator, _z))));
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _z = $new("z");
				
				suppose("preservation_of_" + operator + "_under_addition",
						$(FORALL, _x, ",", _y, ",", _z, IN, R,
								$rule($(_x, operator, _y), $($(_x, "+", _z), operator, $(_y, "+", _z)))));
			}
		}
		
		for (final Object operator : array($("<"), $("<="), LE)) {
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("preservation_of_" + operator + "_under_multiplication",
						$(FORALL, _x, ",", _y, IN, R,
								$rule($(0, operator, _x), $(0, operator, _y), $(0, operator, $(_x, "*", _y)))));
			}
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			final Object _z = $new("z");
			
			suppose("transitivity_of_" + LE + "<",
					$(FORALL, _x, ",", _y, ",", _z, IN, R,
							$rule($(_x, LE, _y), $(_y, "<", _z), $(_x, "<", _z))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			final Object _z = $new("z");
			
			suppose("transitivity_of_<" + LE,
					$(FORALL, _x, ",", _y, ",", _z, IN, R,
							$rule($(_x, "<", _y), $(_y, LE, _z), $(_x, "<", _z))));
		}
		
		for (final Object operator : array("<", ">")) {
			final Object _x = $new("x");
			final Object _y = $new("y");
			
			suppose(operator + "_implies_not_equal",
					$(FORALL, _x, ",", _y, IN, R,
							$rule($(_x, operator, _y), $(LNOT, $(_x, "=", _y)))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			
			suppose("<_implies_" + LE,
					$(FORALL, _x, ",", _y, IN, R,
							$rule($(_x, "<", _y), $(_x, LE, _y))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			
			suppose(">_implies_" + GE,
					$(FORALL, _x, ",", _y, IN, R,
							$rule($(_x, ">", _y), $(_x, GE, _y))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			
			suppose("conversion<>",
					$(FORALL, _x, ",", _y, IN, R,
							$($(_x, "<", _y), "=", $(_y, ">", _x))));
		}
		
		{
			final Object _x = $new("x");
			final Object _y = $new("y");
			
			suppose("equality_<" + LE,
					$(FORALL, _x, ",", _y, IN, Z,
							$($(_x, "<", _y), "=", $($(_x, "+", 1), LE, _y))));
		}
		
		{
			final Object _x = $new("x");
			
			suppose("floor_in_" + Z,
					$(FORALL, _x, IN, R,
							$($("floor", _x), IN, Z)));
		}
		
		loadAutoHints();
		
		for (final Object operator : array(LE, "<")){
			subdeduction("preservation_of_" + operator + "_under_nonnegative_multiplication");
			
			{
				final Object _x = subdeductionForallIn("x", R);
				final Object _y = subdeductionForallIn("y", R);
				final Object _z = subdeductionForallIn("z", R);
				
				suppose($(0, operator, _z));
				suppose($(_x, operator, _y));
				
				autobindTrim("preservation_of_" + operator + "_under_addition", _x, _y, $(-1, "*", _x));
				canonicalize(left(proposition(-1)));
				rewrite(name(-2), name(-1), 0);
				
				autobindTrim("preservation_of_" + operator + "_under_multiplication", right(proposition(-1)), _z);
				
				autobindTrim("preservation_of_" + operator + "_under_addition", left(proposition(-1)), right(proposition(-1)), $(_x, "*", _z));
				canonicalize(left(proposition(-1)));
				rewrite(name(-2), name(-1));
				canonicalize(right(proposition(-1)));
				rewrite(name(-2), name(-1));
				
				repeatConclude(3);
			}
			
			buildForallIn3();
			
			conclude();
		}
		
		for (final Object operator : array(LE, "<")) {
			subdeduction("combination_of_" + operator + operator);
			
			{
				final Object _a = subdeductionForallIn("a", R);
				final Object _b = subdeductionForallIn("b", R);
				final Object _c = subdeductionForallIn("c", R);
				final Object _d = subdeductionForallIn("d", R);
				
				suppose($(_a, operator, _b));
				suppose($(_c, operator, _d));
				
				{
					subdeduction();
					
					autobindTrim("preservation_of_" + operator + "_under_addition", _c, _d, $(_b, "-", _c));
					canonicalize(left(proposition(-1)));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				autobindTrim("transitivity_of_" + operator, _a, left(proposition(-1)), right(proposition(-1)));
				
				{
					subdeduction();
					
					autobindTrim("preservation_of_" + operator + "_under_addition", left(proposition(-1)), right(proposition(-1)), _c);
					canonicalize(right(proposition(-1)));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				repeatConclude(4);
			}
			
			buildForallIn4();
			
			conclude();
		}
		
		Sets.testSimplificationOfTypeOfTuple();
		Sets.testVectorAccess();
	}
	
	public static final void buildForallIn3() {
		final Variable vx = new Variable("x");
		final Variable vy = new Variable("y");
		final Variable vz = new Variable("z");
		final Variable vX = new Variable("X");
		final Variable vP = new Variable("P");
		
		Variable.matchOrFail(
				$forall(vx, $rule($(vx, IN, vX),
						$forall(vy, $rule($(vy, IN, vX),
								$forall(vz, $rule($(vz, IN, vX),
										vP)))))), proposition(-1));
		
		subdeduction();
		
		autobindTrim("definition_of_forall_in_3", vx.get(), vy.get(), vz.get(), vX.get(), vP.get());
		rewriteRight(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void buildForallIn4() {
		final Variable va = new Variable("a");
		final Variable vb = new Variable("b");
		final Variable vc = new Variable("c");
		final Variable vd = new Variable("d");
		final Variable vX = new Variable("X");
		final Variable vP = new Variable("P");
		
		Variable.matchOrFail(
				$forall(va, $rule($(va, IN, vX),
						$forall(vb, $rule($(vb, IN, vX),
								$forall(vc, $rule($(vc, IN, vX),
										$forall(vd, $rule($(vd, IN, vX),
												vP)))))))), proposition(-1));
		
		subdeduction();
		
		autobindTrim("definition_of_forall_in_4", va.get(), vb.get(), vc.get(), vd.get(), vX.get(), vP.get());
		rewriteRight(name(-2), name(-1));
		
		conclude();
	}
	
	public static final Object subdeductionForallIn(final String variableName, final Object type) {
		subdeduction();
		
		final Object result = forall(variableName);
		
		suppose($(result, IN, type));
		
		return result;
	}
	
	public static final void repeatConclude(final int n) {
		for (int i = 0; i < n; ++i) {
			conclude();
		}
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
			
			hintAutodeduce(tryMatch($(vx, IN, N), (e, m) -> {
				autobindTrim("conversion_from_" + Z + "_to_" + N, vx.get());
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			
			hintAutodeduce(tryMatch($($("floor", vx), IN, Z), (e, m) -> {
				autobindTrim("floor_in_" + Z, vx.get());
				
				return true;
			}));
		}
		
		for (int i = 0; i + 1 < NUMERIC_TYPES.length; ++i) {
			final Object _X = NUMERIC_TYPES[i];
			final Object _Y = NUMERIC_TYPES[i + 1];
			final Variable vx = new Variable("x");
			
			hintAutodeduce(tryMatch($(vx, IN, _Y), (e, m) -> {
				final Object _x = vx.get();
				
				subdeduction();
				
				autodeduce($(_x, IN, _X));
				autobindTrim("definition_of_subset", _X, _Y);
				rewrite(existingJustificationFor($(_X, SUBSET, _Y)).getName(), name(-1));
				autobindTrim(name(-1), _x);
				
				conclude();
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			
			hintAutodeduce(tryMatch($(vx, IN, N), (e, m) -> {
				final Object _x = vx.get();
				final Variable vn = v("n");
				final List<Pair<PropositionDescription, PatternMatching>> justifications = potentialJustificationsFor($(_x, IN, $(N, "_", $("<", vn))));
				final Deduction deduction = deduction();
				
				for (final Pair<PropositionDescription, PatternMatching> pair : justifications) {
					final Object _n = pair.getSecond().getMapping().get(vn);
					try {
						subdeduction();
						
						autobindTrim("definition_of_range", _n, _x);
						rewrite(pair.getFirst().getName(), name(-1));
						Propositions.deduceConjunctionLeft(name(-1));
						
						conclude();
						
						return true;
					} catch (final AbortException exception) {
						throw exception;
					} catch (final Exception exception) {
						ignore(exception);
						
						popTo(deduction);
					}
				}
				
				return false;
			}));
		}
		
		for (final Object type : NUMERIC_TYPES) {
			for (final Object operator : array($("+"), $("*"))) {
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				hintAutodeduce(tryMatch($($(vx, operator, vy), IN, type), (e, m) -> {
					autobindTrim("stability_of_" + operator + "_in_" + type, vx.get(), vy.get());
					
					return true;
				}));
			}
		}
		
		for (final Object type : RELATIVE_TYPES) {
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			hintAutodeduce(tryMatch($($(vx, "-", vy), IN, type), (e, m) -> {
				autobindTrim("stability_of_-_in_" + type, vx.get(), vy.get());
				
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
		
		{
			final Variable vx = new Variable("x");
			
			hintAutodeduce(tryMatch($(vx, IN, Sets.POS), (e, m) -> {
				subdeduction();
				
				final Object _x = vx.get();
				
				autodeduce($(_x, IN, N));
				autodeduce($(0, "<", _x));
				autobindTrim("introduction_of_conjunction", proposition(-2), proposition(-1));
				bind("definition_of_positives", _x);
				rewriteRight(name(-2), name(-1));
				
				conclude();
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vn = new Variable("n");
			
			hintAutodeduce(tryMatch($(vx, IN, $(N, "_", $("<", vn))), (e, m) -> {
				subdeduction();
				
				final Object _x = vx.get();
				final Object _n = vn.get();
				
				autodeduce($(_x, IN, N));
				autodeduce($(_x, "<", _n));
				autobindTrim("introduction_of_conjunction", proposition(-2), proposition(-1));
				autobind("definition_of_range", _n, _x);
				rewriteRight(name(-2), name(-1));
				
				conclude();
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			
			hintAutodeduce(tryMatch($(0, LE, vx), (e, m) -> {
				final Object _x = vx.get();
				
				subdeduction();
				
				canonicalize(_x);
				autobindTrim("nonnegativity_of_naturals", right(proposition(-1)));
				rewriteRight(name(-1), name(-2));
				
				conclude();
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			hintAutodeduce(tryMatch($(vx, ">", vy), (e, m) -> {
				final Object _x = vx.get();
				final Object _y = vy.get();
				
				subdeduction();
				
				autodeduce($(_y, "<", _x));
				autobindTrim("conversion<>", left(proposition(-1)), right(proposition(-1)));
				rewrite(name(-2), name(-1));
				
				conclude();
				
				return true;
			}));
		}
		
		{
			final Variable vx = new Variable("x");
			
			hintAutodeduce(tryMatch($(0, LE, vx), (e, m) -> {
				final Object _x = vx.get();
				
				autobindTrim("<_implies_" + LE, 0, _x);
				
				return true;
			}));
		}
		
		for (final Object op : array(LE, "<")) {
			{
				final Variable vx = new Variable("x");
				
				hintAutodeduce(tryMatch($(0, op, vx), (e, m) -> {
					final Object _x = vx.get();
					
					subdeduction();
					
					canonicalize(_x);
					
					final Object _xx = right(proposition(-1));
					
					{
						subdeduction();
						
						final Map<Object, LeftBound> leftBounds = new LinkedHashMap<>();
						final Map<Object, BigDecimal> rightBounds = new LinkedHashMap<>();
						
						new ExpressionVisitor<Void>() {
							
							@Override
							public final Void visit(final Object expression) {
								final Variable va = new Variable("?");
								
								{
									final Deduction deduction = deduction();
									
									try {
										autodeduce($(0, LE, expression));
									} catch (final AbortException exception) {
										throw exception;
									} catch (final Exception exception) {
										popTo(deduction);
									}
								}
								
								for (final Pair<PropositionDescription, PatternMatching> d : potentialJustificationsFor($(va, LE, expression))) {
									final BigDecimal n = cast(BigDecimal.class, $n(d.getSecond().getMapping().get(va)));
									
									if (n != null) {
										leftBounds.computeIfAbsent(expression, __ -> new LeftBound()).update(n, false);
									}
								}
								
								for (final Pair<PropositionDescription, PatternMatching> d : potentialJustificationsFor($(va, "<", expression))) {
									final BigDecimal n = cast(BigDecimal.class, $n(d.getSecond().getMapping().get(va)));
									
									if (n != null) {
										leftBounds.computeIfAbsent(expression, __ -> new LeftBound()).update(n, true);
									}
								}
								
								return null;
							}
							
							@Override
							public final Void visit(final List<?> expression) {
								ExpressionVisitor.super.visit(expression);
								
								final Variable vx = new Variable("x");
								final Variable vy = new Variable("y");
								
								if (match($(vx, "+", vy), expression)) {
									final Object _x = vx.get();
									final Object _y = vy.get();
									final BigDecimal nx = $N(_x);
									final BigDecimal ny = $N(_y);
									
									{
										final LeftBound a = leftBounds.get(_y);
										
										if (nx != null && a != null) {
											if (a.isStrict()) {
												autobindTrim("preservation_of_<_under_addition", a.getValue(), _y, nx);
											} else {
												autobindTrim("preservation_of_≤_under_addition", a.getValue(), _y, nx);
											}
											autobindTrim("commutativity_of_+_in_" + R, left(right(proposition(-1))), right(right(proposition(-1))));
											rewrite(name(-2), name(-1));
											canonicalize(left(proposition(-1)));
											rewrite(name(-2), name(-1));
											leftBounds.put(expression, a.copy().add(nx));
										}
									}
									
									{
										final LeftBound a = leftBounds.get(_x);
										
										if (a != null && ny != null) {
											if (a.isStrict()) {
												autobindTrim("preservation_of_<_under_addition", a.getValue(), _x, ny);
											} else {
												autobindTrim("preservation_of_≤_under_addition", a.getValue(), _x, ny);
											}
											
											canonicalize(left(proposition(-1)));
											rewrite(name(-2), name(-1));
											leftBounds.put(expression, a.copy().add(ny));
										}
									}
								}
								
								if (match($(vx, "*", vy), expression)) {
									final Object _x = vx.get();
									final Object _y = vy.get();
									final BigDecimal nx = $N(_x);
									final BigDecimal ny = $N(_y);
									
									{
										final LeftBound a = leftBounds.get(_y);
										
										if (nx != null && a != null) {
											if (0 <= nx.signum()) {
												if (a.isStrict()) {
													autobindTrim("preservation_of_<_under_nonnegative_multiplication", a.getValue(), _y, nx);
												} else {
													autobindTrim("preservation_of_≤_under_nonnegative_multiplication", a.getValue(), _y, nx);
												}
												autobindTrim("commutativity_of_*_in_" + R, left(right(proposition(-1))), right(right(proposition(-1))));
												rewrite(name(-2), name(-1));
												canonicalize(left(proposition(-1)));
												rewrite(name(-2), name(-1));
												leftBounds.put(expression, a.copy().multiply(nx));
											} else {
												debugPrint("TODO");
//												abort();
											}
										}
									}
									
									{
										final LeftBound a = leftBounds.get(_x);
										
										if (a != null && ny != null) {
											if (0 <= ny.signum()) {
												if (a.isStrict()) {
													autobindTrim("preservation_of_<_under_nonnegative_multiplication", a.getValue(), _x, ny);
												} else {
													autobindTrim("preservation_of_≤_under_nonnegative_multiplication", a.getValue(), _x, ny);
												}
												
												canonicalize(left(proposition(-1)));
												rewrite(name(-2), name(-1));
												leftBounds.put(expression, a.copy().add(ny));
											} else {
												debugPrint("TODO");
//												abort();
											}
										}
									}
								}
								
								return null;
							}
							
							private static final long serialVersionUID = 7743324648699993537L;
							
						}.apply(_xx);
						
						if (_xx instanceof Number) {
							autodeduce($(0, "<", _xx));
						} else {
							final LeftBound a = leftBounds.get(_xx);
							
							if (LE.equals(op)) {
								if (a.isStrict()) {
									autobindTrim("<_implies_" + LE, a.getValue(), _xx);
								}
								
								autobindTrim("transitivity_of_≤", 0, a.getValue(), _xx);
							} else {
								if (!a.getValue().equals($(0))) {
									if (a.isStrict()) {
										autobindTrim("transitivity_of_<", 0, a.getValue(), _xx);
									} else {
										autobindTrim("transitivity_of_<≤", 0, a.getValue(), _xx);
									}
								} else {
									autodeduce($(0, "<", _xx));
								}
							}
						}
						
						conclude();
					}
					
					rewriteRight(name(-1), name(-2));
					
					conclude();
					
					return true;
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				hintAutodeduce(tryMatch($(vx, op, vy), (e, m) -> {
					final Object _x = vx.get();
					final Object _y = vy.get();
					
					if (match($(0), _x)) {
						return false;
					}
					
					subdeduction();
					
					canonicalize(_y);
					
					final Object _yy = right(proposition(-1));
					
					{
						subdeduction();
						
						autodeduce($(0, op, $(_yy, "-", _x)));
						
						autobindTrim("preservation_of_" + op + "_under_addition", left(proposition(-1)), right(proposition(-1)), _x);
						canonicalize(left(proposition(-1)));
						rewrite(name(-2), name(-1));
						canonicalize(right(proposition(-1)));
						rewrite(name(-2), name(-1));
						
						conclude();
					}
					
					rewriteRight(name(-1), name(-2));
					
					conclude();
					
					return true;
				}));
			}
		}
		
	}
	
	/**
	 * @author codistmonk (creation 2016-09-07)
	 */
	public static final class LeftBound implements Serializable {
		
		private BigDecimal value;
		
		private boolean strict;
		
		public final LeftBound copy() {
			return new LeftBound().update(this.getValue(), this.isStrict());
		}
		
		public final BigDecimal getValue() {
			return this.value;
		}
		
		public final boolean isStrict() {
			return this.strict;
		}
		
		public final LeftBound update(final BigDecimal value, final boolean strict) {
			if (this.getValue() == null) {
				this.value = value;
				this.strict = strict;
			} else {
				final int cmp = this.getValue().compareTo(value);
				
				if (cmp == 0) {
					this.strict |= strict;
				} else if (cmp < 0) {
					this.value = value;
					this.strict = strict;
				}
			}
			
			return this;
		}
		
		public final LeftBound add(final BigDecimal delta) {
			this.value = this.value.add(delta);
			
			return this;
		}
		
		public final LeftBound multiply(final BigDecimal delta) {
			this.value = this.value.multiply(delta);
			
			return this;
		}
		
		@Override
		public final String toString() {
			return this.getValue() + (this.isStrict() ? "<" : LE.toString());
		}
		
		private static final long serialVersionUID = -6609892525772921169L;
		
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
			
			if (match($(0, "+", vx), e)) {
				autobindTrim("neutrality_of_0", vx.get());
				
				return true;
			}
			
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
			return $N(object1).compareTo($N(object2));
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
			final Variable vz = new Variable("y");
			
			if (match($(0, "*", vx), e)) {
				autobindTrim("absorbingness_of_0", vx.get());
				
				return true;
			}
			
			if (match($(1, "*", vx), e)) {
				autobindTrim("neutrality_of_1", vx.get());
				
				return true;
			}
			
			if (match($(vx, "*", $(vy, "+", vz)), e)) {
				final Object _x = vx.get();
				final Object _y = vy.get();
				final Object _z = vz.get();
				
				autobindTrim("distributivity_of_*_over_+", _x, _y, _z);
				
				return true;
			}
			
			if (match($($(vx, "+", vy), "*", vz), e)) {
				final Object _x = vx.get();
				final Object _y = vy.get();
				final Object _z = vz.get();
				
				subdeduction();
				
				autobindTrim("distributivity_of_*_over_+", _z, _x, _y);
				autobindTrim("commutativity_of_*_in_" + R, left(left(proposition(-1))), right(left(proposition(-1))));
				rewrite(name(-2), name(-1));
				
				conclude();
				
				return true;
			}
			
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
