package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.deductions.Sequences.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.proofs.Stack.*;
import static autodiff.reasoning.tactics.PatternPredicate.rule;
import static autodiff.rules.Variable.match;
import static multij.tools.Tools.*;

import autodiff.nodes.Computation.RepeatHelper;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.Stack.AbortException;
import autodiff.rules.Rules;
import autodiff.rules.Variable;

import java.util.List;

import multij.tools.IllegalInstantiationException;
import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-08-27)
 */
public final class Sets {
	
	private Sets() {
		throw new IllegalInstantiationException();
	}
	
	public static final Object U = $("℧");
	
	public static final Object P = $("ℙ");
	
	public static final Object POS = $(N, "_", $(">", 0));
	
	public static final Object SUBSET = $("⊂");
	
	public static final Object CROSS = $("×");
	
	public static final void setup() {
		supposeDefinitionOfForallIn();
		supposeDefinitionOfForallIn2();
		supposeDefinitionOfForallIn3();
		
		supposeDefinitionOfSubset();
		supposeDefinitionOfPowerset();
		supposeSubsetInUhm();
		
		deduceTransitivityOfSubset();
		
		supposeVectorTypeInUhm();
		
		supposeTypeOfSingle();
		supposeTypeOfSingleInUhm();
		
		supposeTypeOfTuple();
		supposeTypeOfTupleInUhm();
		
		supposeRealsInUhm();
		supposeNaturalsSubsetReals();
		deduceNaturalsInUhm();
		supposeDefinitionOfPositives();
		
		{
			suppose("reals_single_in_Uhm",
					$($1(R), IN, U));
		}
		
		{
			subdeduction("single_N_in_Uhm");
			
			ebindTrim("type_of_single_in_Uhm", N);
			
			conclude();
		}
		
		testTypeOfTuple();
		
		supposeDefinitionsForRepeat();
		
		supposeSimplificationOfTypeOfTuple();
		testSimplificationOfTypeOfTuple();
		
		supposeDefinitionsForVectorAccess();
		testVectorAccess();
	}
	
	public static final void supposeRealsInUhm() {
		suppose("reals_in_Uhm",
				$(R, IN, U));
	}
	
	public static final void supposeNaturalsSubsetReals() {
		suppose("naturals_subset_reals",
				$(N, SUBSET, R));
	}
	
	public static final void deduceNaturalsInUhm() {
		subdeduction("naturals_in_Uhm");
		
		ebindTrim("subset_in_Uhm", N, R);
		
		conclude();
	}
	
	public static final void supposeDefinitionOfPositives() {
		final Object _n = $new("n");
		
		suppose("definition_of_positives", $forall(_n,
				$($(_n, IN, POS), "=", $($(_n, IN, N), LAND, $(0, "<", _n)))));
	}
	
	public static final void supposeDefinitionOfForallIn() {
		final Object _x = $new("x");
		final Object _X = $new("X");
		final Object _P = $new("P");
		
		suppose("definition_of_forall_in", $forall(_x, _X, _P,
				$($(FORALL, _x, IN, _X, _P), "=", $forall(_x, $rule($(_x, IN, _X), _P)))));
	}
	
	public static final void supposeDefinitionOfForallIn2() {
		final Object _x = $new("x");
		final Object _y = $new("y");
		final Object _X = $new("X");
		final Object _P = $new("P");
		
		suppose("definition_of_forall_in_2", $forall(_x, _y, _X, _P,
				$($(FORALL, _x, ",", _y, IN, _X, _P), "=", $forall(_x, $rule($(_x, IN, _X), $forall(_y, $rule($(_y, IN, _X), _P)))))));
	}
	
	public static final void supposeDefinitionOfForallIn3() {
		final Object _x = $new("x");
		final Object _y = $new("y");
		final Object _z = $new("z");
		final Object _X = $new("X");
		final Object _P = $new("P");
		
		suppose("definition_of_forall_in_3", $forall(_x, _y, _z, _X, _P,
				$($(FORALL, _x, ",", _y, ",", _z, IN, _X, _P),
						"=", $forall(_x, $rule($(_x, IN, _X), $forall(_y, $rule($(_y, IN, _X), $forall(_z, $rule($(_z, IN, _X), _P)))))))));
	}
	
	public static final void supposeDefinitionOfSubset() {
		final Object _x = $new("x");
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("definition_of_subset", $forall(_X, $(FORALL, _Y, IN, U,
				$($(_X, SUBSET, _Y), "=", $forall(_x, $rule($(_x, IN, _X), $(_x, IN, _Y)))))));
	}
	
	public static final void supposeDefinitionOfPowerset() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("definition_of_powerset", $forall(_X, _Y,
				$($(_X, IN, pp(_Y)), "=", $(_X, SUBSET, _Y))));
	}
	
	public static final void supposeSubsetInUhm() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("subset_in_Uhm",
				$forall(_X,
						$(FORALL, _Y, IN, U,
								$rule($(_X, SUBSET, _Y), $(_X, IN, U)))));
	}
	
	public static final void deduceTransitivityOfSubset() {
		subdeduction("transitivity_of_subset");
		
		final Object _X = forall("X");
		final Object _Y = forall("Y");
		final Object _Z = forall("Z");
		
		suppose($(_X, IN, U));
		suppose($(_Y, IN, U));
		suppose($(_Z, IN, U));
		suppose($(_X, SUBSET, _Y));
		suppose($(_Y, SUBSET, _Z));
		
		final String h1 = name(-2);
		final String h2 = name(-1);
		
		{
			subdeduction();
			
			final Object _x = forall("x");
			
			suppose($(_x, IN, _X));
			
			final String h3 = name(-1);
			
			{
				subdeduction();
				
				ebindTrim("definition_of_subset", _X, _Y);
				rewrite(h1, name(-1));
				bind(name(-1), _x);
				
				conclude();
			}
			
			apply(name(-1), h3);
			
			{
				subdeduction();
				
				ebindTrim("definition_of_subset", _Y, _Z);
				rewrite(h2, name(-1));
				bind(name(-1), _x);
				
				conclude();
			}
			
			apply(name(-1), name(-2));
			
			conclude();
		}
		
		{
			subdeduction();
			
			ebindTrim("definition_of_subset", _X, _Z);
			
			conclude();
		}
		
		rewriteRight(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void supposeVectorTypeInUhm() {
		final Object _X = $new("X");
		final Object _n = $new("n");
		
		suppose("vector_type_in_Uhm",
				
				$(FORALL, _X, IN, U,
						$(FORALL, _n, IN, N,
								$($(_X, "^", _n), IN, U))));
	}
	
	public static final void supposeTypeOfSingle() {
		final Object _X = $new("X");
		final Object _x = $new("x");
		
		suppose("type_of_single",
				$(FORALL, _X, IN, U,
						$forall(_x,
								$($(_x, IN, _X), "=", $($1(_x), IN, $1(_X))))));
	}
	
	public static final void supposeTypeOfSingleInUhm() {
		final Object _X = $new("X");
		
		suppose("type_of_single_in_Uhm",
				$(FORALL, _X, IN, U,
						$($1(_X), IN, U)));
	}
	
	public static final void supposeTypeOfTuple() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		final Object _x = $new("x");
		final Object _y = $new("y");
		
		suppose("type_of_tuple",
				$(FORALL, _X, ",", _Y, IN, U,
						$(FORALL, _x, IN, _X,
								$(FORALL, _y, IN, _Y,
										$($("sequence_append", ",", _x, _y), IN, $("sequence_append", CROSS, _X, _Y))))));
	}
	
	public static final void supposeTypeOfTupleInUhm() {
		final Object _X = $new("X");
		final Object _Y = $new("Y");
		
		suppose("type_of_tuple_in_Uhm",
				$(FORALL, _X, ",", _Y, IN, U,
						$($("sequence_append", CROSS, _X, _Y), IN, U)));
	}
	
	public static final void testTypeOfTuple() {
		{
			subdeduction("type_of_tuple.test1");
			
			{
				subdeduction();
				
				verifyElementaryProposition($(1, IN, N));
				
				ebindTrim("type_of_single", N, 1);
				
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			ebindTrim("type_of_tuple", $1(N), N, $1(1), 2);
			
			final List<?> _x = list(left(proposition(-1)));
			final List<?> _X = list(right(proposition(-1)));
			
			computeSequenceAppend(_x.get(1), _x.get(2), _x.get(3));
			rewrite(name(-2), name(-1));
			
			computeSequenceAppend(_X.get(1), _X.get(2), _X.get(3));
			rewrite(name(-2), name(-1));
			
			conclude();
		}
		
		{
			subdeduction("type_of_tuple.test2");
			
			{
				subdeduction();
				
				ebindTrim("type_of_tuple_in_Uhm", $1(N), N);
				
				computeSequenceAppend(CROSS, $1(N), N);
				rewrite(name(-2), name(-1));
				
				conclude();
			}
			
			ebindTrim("type_of_tuple", sequence(CROSS, N, N), N, sequence(",", 1, 2), 3);
			
			final List<?> _x = list(left(proposition(-1)));
			final List<?> _X = list(right(proposition(-1)));
			
			computeSequenceAppend(_x.get(1), _x.get(2), _x.get(3));
			rewrite(name(-2), name(-1));
			
			computeSequenceAppend(_X.get(1), _X.get(2), _X.get(3));
			rewrite(name(-2), name(-1));
			
			conclude();
		}
	}
	
	public static final void supposeDefinitionsForRepeat() {
		{
			final Object _s = $new("s");
			final Object _x = $new("x");
			
			suppose("definition_of_repeat_0",
					$forall(_s, _x,
							$($("repeat", _s, _x, 0), "=", $())));
		}
		
		{
			final Object _s = $new("s");
			final Object _x = $new("x");
			final Object _n = $new("n");
			
			suppose("definition_of_repeat_n",
					$forall(_s, _x,
							$(FORALL, _n, IN, POS,
									$($("repeat", _s, _x, _n), "=", $("sequence_append", _s, $("repeat", _s, _x, $(_n, "-", 1)), _x)))));
		}
	}
	
	public static final void supposeSimplificationOfTypeOfTuple() {
		final Object _n = $new("n");
		final Object _X = $new("X");
		
		suppose("simplification_of_type_of_tuple",
				$(FORALL, _X, IN, U,
						$(FORALL, _n, IN, N,
								$($("repeat", CROSS, _X, _n), "=", $(_X, "^", _n)))));
	}
	
	public static final void testSimplificationOfTypeOfTuple() {
		{
			subdeduction("simplification_of_type_of_tuple.test1");
			
			ebindTrim("simplification_of_type_of_tuple", N, 3);
			
			new RepeatHelper(CROSS, N, 3).compute();
			rewrite(name(-2), name(-1));
			
			conclude();
		}
		
		{
			subdeduction("simplification_of_type_of_tuple.test2");
			
			rewrite("type_of_tuple.test2", "simplification_of_type_of_tuple.test1");
			
			conclude();
		}
	}
	
	public static final void supposeDefinitionsForVectorAccess() {
		{
			final Object _x = $new("x");
			final Object _X = $new("X");
			final Object _n = $new("n");
			
			suppose("definition_of_vector_access_0",
					$(FORALL, _X, IN, U,
							$(FORALL, _n, IN, POS,
									$(FORALL, _x, IN, $(_X, "^", _n),
											$($(_x, "_", 0), "=", $("sequence_head", _x))))));
		}
		
		{
			final Object _x = $new("x");
			final Object _X = $new("X");
			final Object _n = $new("n");
			final Object _i = $new("i");
			
			suppose("definition_of_vector_access_i",
					$(FORALL, _X, IN, U,
							$(FORALL, _n, ",", _i, IN, POS,
									$(FORALL, _x, IN, $(_X, "^", _n),
											$($(_x, "_", _i), "=", $($("sequence_tail", ",", _x), "_", $(_i, "-", 1)))))));
		}
	}
	
	public static final void testVectorAccess() {
		{
			subdeduction("vector_access.test1");
			
			computeVectorAccess(R, $(sequence(",", 1, 2, 3), "_", 1));
			
			conclude();
		}
	}
	
	
	public static final void supposeDefinitionOfSingleton() {
		final Object _X = $new("X");
		
		suppose("definition_of_singleton",
				$forall(_X,
						$(_X, IN, c(_X))));
	}
	
	public static final void computeVectorAccess(final Object elementType, final Object formula) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final Variable _x = new Variable("x");
			
			rules.add(rule($(_x, "_", 0), (__, m) -> {
				{
					subdeduction();
					
					ebindTrim("definition_of_vector_access_0", elementType, sequenceLength(",", m.get(_x)), m.get(_x));
					computeSequenceHead(m.get(_x));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		{
			final Variable _x = new Variable("x");
			final Variable _i = new Variable("i");
			
			rules.add(rule($(_x, "_", _i), (__, m) -> {
				{
					subdeduction();
					
					ebindTrim("definition_of_vector_access_i", elementType, sequenceLength(",", m.get(_x)), m.get(_i), m.get(_x));
					simplifyElementaryExpression(name(-1), right(right(proposition(-1))));
					
					computeSequenceTail(",", m.get(_x));
					rewrite(name(-2), name(-1));
					
					computeVectorAccess(elementType, right(proposition(-1)));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		rules.applyTo(formula);
	}
	
	public static final Object pp(final Object... set) {
		return $(P, p(set));
	}
	
	public static final List<Object> p(final Object... objects) {
		return list($("(", $(objects), ")"));
	}
	
	public static final List<Object> c(final Object... objects) {
		return list($("{", $(objects), "}"));
	}
	
	public static final void ebindLast(final Object... values) {
		ebind(name(-1), values);
	}
	
	public static final void ebindTrim(final String target, final Object... values) {
		subdeduction();
		
		ebind(target, values);
		trimLast();
		
		conclude();
	}
	
	public static final void ebind(final String target, final Object... values) {
		subdeduction();
		
		String newTarget = target;
		
		for (final Object value : values) {
			ebind1(newTarget, value);
			newTarget = name(-1);
		}
		
		conclude();
	}
	
	public static final void ebind1(final String target, final Object value) {
		subdeduction();
		
		String newTarget = target;
		boolean done = false;
		
		while (!done) {
//		while (!isBlock(proposition(newTarget))) {
//			debugPrint(proposition(newTarget));
			
			done = true;
			
			if (isForallIn(proposition(newTarget))) {
				canonicalizeForallIn(newTarget);
				newTarget = name(-1);
				done = false;
			} else if (isForallIn2(proposition(newTarget))) {
				canonicalizeForallIn2(newTarget);
				newTarget = name(-1);
				done = false;
			} else if (isForallIn3(proposition(newTarget))) {
				canonicalizeForallIn3(newTarget);
				newTarget = name(-1);
				done = false;
			} else if (trim(newTarget)) {
				newTarget = name(-1);
				done = false;
			}
		}
		
		bind(newTarget, value);
		
		conclude();
	}
	
	public static final void trimLast() {
		trim(name(-1));
	}
	
	public static final boolean trim(final String target) {
		if (isRule(proposition(target))) {
			String newTarget = target;
			
			subdeduction();
			
			while (isRule(proposition(newTarget))) {
				eapply(newTarget);
				newTarget = name(-1);
			}
			
			conclude();
			
			return true;
		}
		
		return false;
	}
	
	public static final void eapplyLast() {
		eapply(name(-1));
	}
	
	public static final void eapply(final String targetName) {
		subdeduction();
				
		final String justificationName = justicationFor(condition(proposition(targetName))).getName();
		
		apply(targetName, justificationName);
		
		conclude();
	}
	
	public static final PropositionDescription justicationFor(final Object proposition) {
		PropositionDescription result = PropositionDescription.existingJustificationFor(proposition);
		
		if (result == null) {
			{
				final Deduction deduction = deduction();
				
				try {
					verifyElementaryProposition(proposition);
				} catch (final Exception exception) {
					ignore(exception);
					
					while (deduction() != deduction) {
						pop();
					}
					
					if (isIdentity(proposition)) {
						bind("identity", left(proposition));
					} else if (isArithmeticTyping(proposition)) {
						return justifyArithmeticTyping(proposition);
					} else if (isPositivity(proposition)) {
						deducePositivity(left(proposition));
					} else if(isCartesianProductity(proposition)) {
						deduceCartesianProduct(left(right(proposition)), flattenSequence(",", left(proposition)).toArray());
					} else {
						throw new IllegalStateException("Failed to justify: " + proposition);
					}
				}
			}
			
			result = new PropositionDescription()
			.setIndex(-1)
			.setName(name(-1))
			.setProposition(proposition(-1));
		}
		
		return result;
	}
	
	public static final void deduceCartesianProduct(final Object valueType, final Object... values) {
		subdeduction();
		
		beginCartesianProduct(values[0], valueType);
		
		for (int i = 1; i < values.length; ++i) {
			appendToCartesianProduct(values[i], valueType);
		}
		
		{
			subdeduction();
			
			ebindTrim("simplification_of_type_of_tuple", valueType, values.length);
			
			new RepeatHelper(CROSS, valueType, values.length).compute();
			rewrite(name(-2), name(-1));
			
			conclude();
		}
		
		rewrite(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void beginCartesianProduct(final Object value,
			final Object type) {
		subdeduction();
		
		deduceSingleType(justicationFor($(value, IN, type)).getName());
		
		conclude();
	}
	
	public static final void appendToCartesianProduct(final Object value, final Object type) {
		final Object previousValue = left(proposition(-1));
		final Object previousType = right(proposition(-1));
		
		{
			subdeduction();
			
			ebindTrim("type_of_tuple_in_Uhm", previousType, type);
			
//			new SequenceAppendHelper(CROSS, previousType, type).compute();
			computeSequenceAppend(CROSS, previousType, type);
			rewrite(name(-2), name(-1));
			
			conclude();
		}
		
		{
			subdeduction();
			
			deducePositivity(1);
			
			ebindTrim("type_of_tuple", previousType, type, previousValue, value);
			
//			new SequenceAppendHelper(",", previousValue, value).compute();
			computeSequenceAppend(",", previousValue, value);
			rewrite(name(-2), name(-1));
			
//			new SequenceAppendHelper(CROSS, previousType, type).compute();
			computeSequenceAppend(CROSS, previousType, type);
			rewrite(name(-2), name(-1));
			
			conclude();
		}
	}
	
	public static final void deduceSingleType(final String targetName) {
		final Object proposition = proposition(targetName);
		
		subdeduction();
		
		{
			subdeduction();
			
			ebindTrim("type_of_single", right(proposition), left(proposition));
			
			conclude();
		}
		
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
	public static final PropositionDescription justifyArithmeticTyping(final Object proposition) {
		PropositionDescription result = PropositionDescription.existingJustificationFor(proposition);
		
		if (result != null) {
			return result;
		}
		
		try {
			verifyElementaryProposition(proposition);
			
			result = new PropositionDescription().setIndex(-1).setName(name(-1)).setProposition(proposition(-1));
		} catch (final AbortException exception) {
			throw exception;
		} catch (final Exception exception) {
			ignore(exception);
		}
		
		if (result != null) {
			return result;
		}
		
		final Object type = right(proposition);
		
//		if (R.equals(type)) {
//			subdeduction();
//			
//			PropositionDescription tmp = justifyArithmeticTyping($(left(proposition), IN, Q));
//			
//			if (tmp != null) {
//				try {
//					subdeduction();
//					
//					ebindTrim("definition_of_subset", Q, R);
//					rewrite("rationals_subset_reals", name(-1));
//					ebindTrim(name(-1), left(proposition));
//					
//					conclude();
//				} catch (final AbortException exception) {
//					throw exception;
//				} catch (final Exception exception) {
//					ignore(exception);
//					
//					pop();
//				}
//			}
//		}
		
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final Variable vx = new Variable("x");
			final Variable vy = new Variable("y");
			
			rules.add(rule($(vx, "+", vy), (e, m) -> {
				{
					subdeduction();
					
					final Object x = vx.get();
					final Object y = vy.get();
					final PropositionDescription jx = justifyArithmeticTyping($(x, IN, type));
					final PropositionDescription jy = justifyArithmeticTyping($(y, IN, type));
					
					if (jx != null && jy != null) {
						ebindTrim("stability_of_addition_in_" + type, x, y);
						
						conclude();
					} else {
						pop();
					}
				}
				
				return null;
			}));
		}
		
		rules.applyTo(left(proposition));
		
		result = new PropositionDescription().setIndex(-1).setName(name(-1)).setProposition(proposition(-1));
		
		return result;
	}
	
	public static final boolean isIdentity(final Object expression) {
		final List<?> list = cast(List.class, expression);
		
		return 3 == list.size() && "=".equals(operator(expression)) && left(expression).equals(right(expression));
	}
	
	public static final boolean isCartesianProductity(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		if (list != null && 3 == list.size() && IN.equals(middle(list))) {
			final List<?> type = cast(List.class, right(list));
			
			return type != null && "^".equals(middle(type));
		}
		
		return false;
	}
	
	public static final boolean isArithmeticTyping(final Object proposition) {
		final Variable vt = new Variable("T");
		
		if (match($(new Variable("*"), IN, vt), proposition)) {
			return Tools.set(N, R).contains(vt.get());
		}
		
		return false;
	}
	
	public static final boolean isPositivity(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 3 == list.size()
				&& IN.equals(middle(list)) && POS.equals(right(list));
	}
	
	public static final boolean isNaturality(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 3 == list.size()
				&& IN.equals(middle(list)) && N.equals(right(list));
	}
	
	public static final boolean isReality(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 3 == list.size()
				&& IN.equals(middle(list)) && R.equals(right(list));
	}
	
	public static final boolean isForallIn(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 5 == list.size()
				&& FORALL.equals(list.get(0)) && IN.equals(list.get(2));
	}
	
	public static final boolean isForallIn2(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 7 == list.size()
				&& FORALL.equals(list.get(0)) && ",".equals(list.get(2)) && IN.equals(list.get(4));
	}
	
	public static final boolean isForallIn3(final Object proposition) {
		final List<?> list = cast(List.class, proposition);
		
		return list != null && 9 == list.size()
				&& FORALL.equals(list.get(0)) && ",".equals(list.get(2)) && ",".equals(list.get(4)) && IN.equals(list.get(6));
	}
	
	public static final void deducePositivity(final Object target) {
		subdeduction();
		
		bind("definition_of_positives", target);
		
		{
			subdeduction();
			
			final PropositionDescription j1 = justicationFor($(target, IN, N));
			final PropositionDescription j2 = justicationFor($(0, "<", target));
			
			ebindTrim("introduction_of_conjunction", j1.getProposition(), j2.getProposition());
			
			conclude();
		}
		
		rewriteRight(name(-1), name(-2));
		
		conclude();
	}
	
	public static final void canonicalizeForallIn(final Object target) {
		final List<Object> list = list(target);
		
		bind("definition_of_forall_in", list.get(1), list.get(3), list.get(4));
	}
	
	public static final void canonicalizeForallIn(final String targetName) {
		final List<Object> list = list(proposition(targetName));
		
		subdeduction();
		
		bind("definition_of_forall_in", list.get(1), list.get(3), list.get(4));
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
	public static final void compactForallIn(final String targetName) {
		final Object target = proposition(targetName);
		
		subdeduction();
		
		bind("definition_of_forall_in", variable(target), right(condition(scope(target))), conclusion(scope(target)));
		rewriteRight(targetName, name(-1));
		
		conclude();
	}
	
	public static final void canonicalizeForallIn2(final String targetName) {
		final List<Object> list = list(proposition(targetName));
		
		subdeduction();
		
		bind("definition_of_forall_in_2", list.get(1), list.get(3), list.get(5), list.get(6));
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
	public static final void canonicalizeForallIn3(final String targetName) {
		final List<Object> list = list(proposition(targetName));
		
		subdeduction();
		
		bind("definition_of_forall_in_3", list.get(1), list.get(3), list.get(5), list.get(7), list.get(8));
		rewrite(targetName, name(-1));
		
		conclude();
	}
	
}
