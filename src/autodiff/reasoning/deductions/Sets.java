package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.N;
import static autodiff.reasoning.proofs.ElementaryVerification.R;
import static autodiff.reasoning.proofs.Stack.*;
import static autodiff.reasoning.tactics.PatternPredicate.rule;
import static autodiff.rules.Variable.match;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.Iterator;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import autodiff.nodes.Computation.RepeatHelper;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.Substitution;
import autodiff.reasoning.proofs.Stack.AbortException;
import autodiff.rules.Rules;
import autodiff.rules.Variable;

import static multij.tools.Tools.append;
import static multij.tools.Tools.cast;
import static multij.tools.Tools.ignore;

import multij.tools.IllegalInstantiationException;
import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-08-27)
 */
public final class Sets {
	
	private Sets() {
		throw new IllegalInstantiationException();
	}
	
	public static final Object POS = $(N, "_", $(">", 0));
	
	public static final Object SUBSET = $("⊂");
	
	public static final Object CROSS = $("×");
	
	public static final void setup() {
		supposeDefinitionOfForallIn();
		supposeDefinitionOfForallIn2();
		supposeDefinitionOfForallIn3();
		
		{
			final Object _s = $new("s");
			final Object _x = $new("x");
			final Object _y = $new("y");
			
			suppose("definition_of_sequence_new",
					$forall(_s, _x, _y,
							$($("sequence_new", _s, _x, _y), "=", $(_x, $(_s, _y)))));
		}
		
		supposeDefinitionsForSequenceAppend();
		testSequenceAppend();
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
		PropositionDescription result = existingJustificationFor(proposition);
		
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
	
	public static final void computeSequenceAppend(final Object s, final Object x, final Object y) {
		computeSequenceAppend(newName(), s, x, y);
	}
	
	public static final void computeSequenceAppend(final String propositionName, final Object s, final Object x, final Object y) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final CaseDescription c = newSequenceAppendCase0();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), c.getConditions(), v.get("y")), (__, m) -> {
				ebindTrim("definition_of_sequence_append_0", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceAppendCase1();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), c.getConditions(), v.get("y")), (__, m) -> {
				ebindTrim("definition_of_sequence_append_1", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceAppendCase2();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), c.getConditions(), v.get("y")), (__, m) -> {
				{
					subdeduction();
					
					final Object[] values = v.values().stream().map(m::get).toArray();
					
					ebindTrim("definition_of_sequence_append_2", values);
					
					computeSequenceSubappend(s, values[3], y);
					
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		{
			subdeduction(propositionName);
			
			rules.applyTo($(s, $1($(x, "=", x)), y));
			
			conclude();
		}
	}
	
	public static final void computeSequenceSubappend(final Object s, final Object x, final Object y) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final CaseDescription c = newSequenceSubappendCase0();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), c.getConditions(), v.get("y")), (__, m) -> {
				ebindTrim("definition_of_sequence_subappend_0", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceSubappendCase1();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), c.getConditions(), v.get("y")), (__, m) -> {
				{
					subdeduction();
					
					final Object[] values = v.values().stream().map(m::get).toArray();
					
					ebindTrim("definition_of_sequence_subappend_1", values);
					
					computeSequenceSubappend(s, values[3], y);
					
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		rules.applyTo($(s, $1($(x, "=", x)), y));
	}
	
	public static final PropositionDescription existingJustificationFor(final Object proposition) {
		for (final PropositionDescription description : iterateBackward(deduction())) {
			if (new Substitution.ExpressionEquality().apply(proposition, description.getProposition())) {
				return description;
			}
		}
		
		return null;
	}
	
	public static final PropositionDescription justifyArithmeticTyping(final Object proposition) {
		PropositionDescription result = existingJustificationFor(proposition);
		
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
	
	public static final Iterable<PropositionDescription> iterateBackward(final Deduction deduction) {
		return new Iterable<PropositionDescription>() {
			
			@Override
			public final Iterator<PropositionDescription> iterator() {
				return new Iterator<PropositionDescription>() {
					
					private final PropositionDescription result = new PropositionDescription();
					
					private Deduction currentDeduction = deduction;
					
					private int i = this.currentDeduction.getPropositionNames().size();
					
					@Override
					public final boolean hasNext() {
						return 0 < this.i || !isEmpty(this.currentDeduction.getParent());
					}
					
					@Override
					public final PropositionDescription next() {
						if (--this.i < 0) {
							this.currentDeduction = this.currentDeduction.getParent();
							
							while (this.currentDeduction.getPropositionNames().isEmpty()) {
								this.currentDeduction = this.currentDeduction.getParent();
							}
							
							this.i = this.currentDeduction.getPropositionNames().size() - 1;
						}
						
						final String name = this.currentDeduction.getPropositionNames().get(this.i);
						
						return this.result
								.setIndex(this.result.getIndex() - 1)
								.setName(name)
								.setProposition(this.currentDeduction.getPropositions().get(name));
					}
					
				};
			}
			
		};
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
	
	public static final boolean isEmpty(final Deduction deduction) {
		return deduction == null
				|| (deduction.getPropositionNames().isEmpty()
						&& (deduction.getParent() == null || isEmpty(deduction.getParent())));
	}
	
	public static final List<Object> flattenSequence(final Object separator, final Object sequence) {
		final List<Object> result = new ArrayList<>();
		final List<?> list = list(sequence);
		
		if (list.isEmpty()) {
			return Collections.emptyList();
		}
		
		result.add(first(list));
		
		if (2 == list.size()) {
			List<?> tmp = list(second(list));
			
			while (tmp != null) {
				if (2 == tmp.size() && separator.equals(first(tmp))) {
					result.add(second(tmp));
					break;
				}
				
				if (3 == tmp.size() && separator.equals(first(tmp))) {
					result.add(second(tmp));
					tmp = list(tmp.get(2));
				}
			}
		} else if (1 != list.size()) {
			throw new IllegalArgumentException();
		}
		
		return result;
	}
	
	public static final CaseDescription newSequenceAppendCase0() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = $1($(_x, "=", $()));
		final Object value = $1(_y);
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"y", _y),
				conditions,
				$($("sequence_append", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceAppendCase1() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = $1($(_x, "=", $1(_x0)));
		final Object value = $(_x0, $(_s, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"y", _y),
				conditions,
				$($("sequence_append", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceAppendCase2() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _x1 = new Variable("x1");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = $1($(_x, "=", $(_x0, _x1)));
		final Object value = $(_x0, $("sequence_subappend", _s, _x1, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"x1", _x1,
						"y", _y),
				conditions,
				$($("sequence_append", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceSubappendCase0() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_x, "=", $(_s, _x0)));
		final Object value = $(_s, _x0, $(_s, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"y", _y),
				conditions,
				$($("sequence_subappend", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceSubappendCase1() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _x1 = new Variable("x1");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_x, "=", $(_s, _x0, _x1)));
		final Object value = $(_s, _x0, $("sequence_subappend", _s, _x1, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"x1", _x1,
						"y", _y),
				conditions,
				$($("sequence_subappend", _s, _x, _y), "=", value));
	}
	
	public static final void supposeDefinitionsForSequenceAppend() {
		/*
		 * 
		 * append s [] y      = [y]
		 * append s [x0] y    = [x0 [s y]]
		 * append s [x0 x1] y = [x0 (subappend s x1 y)]
		 * 
		 * subappend s [s x0] y    = [s x0 [s y]]
		 * subappend s [s x0 x1] y = [s x0 (subappend s x1 y)]
		 * 
		 */
		
		supposeDefinitions("sequence_append",
				newSequenceAppendCase0(),
				newSequenceAppendCase1(),
				newSequenceAppendCase2());
		
		supposeDefinitions("sequence_subappend",
				newSequenceSubappendCase0(),
				newSequenceSubappendCase1());
	}
	
	public static final void supposeDefinitions(final String definedName, final CaseDescription... descriptions) {
		final int n = descriptions.length;
		
		for (int i = 0; i < n; ++i) {
			final CaseDescription caseDescription = descriptions[i].instantiate();
			
			suppose("definition_of_" + definedName + "_" + i,
					$forall(append(caseDescription.getVariables().values().toArray(),
							$rule(append(caseDescription.getConditions().toArray(), caseDescription.getDefinition())))));
		}
		
		for (int i = 0; i < n; ++i) {
			{
				final CaseDescription cI = descriptions[i].instantiate("_i");
				final CaseDescription cJ = descriptions[i].instantiate("_j");
				final Object[] variablesI = cI.getVariables().values().toArray();
				final Object[] variablesJ = cJ.getVariables().values().toArray();
				
				for (int k = 0; k < variablesI.length; ++k) {
					suppose("definition_of_" + definedName + "_inequality_" + i + "_" + i + "_" + k,
							$forall(append(cI.getVariables().values().toArray(),
									$rule(append(cI.getConditions().toArray(),
											$forall(append(cJ.getVariables().values().toArray(),
													$rule(append(cJ.getConditions().toArray(),
															$(LNOT, $(variablesI[k], "=", variablesJ[k])),
															$(LNOT, $(left(cI.getDefinition()), "=", left(cJ.getDefinition()))))))))))));
				}
			}
			
			for (int j = i + 1; j < n; ++j) {
				final CaseDescription cI = descriptions[i].instantiate("_i");
				final CaseDescription cJ = descriptions[j].instantiate("_j");
				
				suppose("definition_of_" + definedName + "_inequality_" + i + "_" + j,
						$forall(append(cI.getVariables().values().toArray(),
								$rule(append(cI.getConditions().toArray(),
										$forall(append(cJ.getVariables().values().toArray(),
												$rule(append(cJ.getConditions().toArray(),
														$(LNOT, $(left(cI.getDefinition()), "=", left(cJ.getDefinition()))))))))))));
			}
		}
	}
	
	public static final void testSequenceAppend() {
		final Object _s = $(",");
		
		{
			final Object _x = sequence(_s, 1);
			final Object _y = 2;
			
			computeSequenceAppend("sequence_append.test1", _s, _x, _y);
		}
		
		{
			final Object _x = sequence(_s, 1, 2);
			final Object _y = 3;
			
			computeSequenceAppend("sequence_append.test2", _s, _x, _y);
		}
		
		{
			final Object _x = sequence(_s, 1, 2, 3);
			final Object _y = 4;
			
			computeSequenceAppend("sequence_append.test3", _s, _x, _y);
		}
	}
	
	public static final Object sequence(final Object separator, final Object... elements) {
		if (elements.length == 0) {
			return $();
		}
		
		if (elements.length == 1) {
			return $1(elements[0]);
		}
		
		List<Object> result = list($(separator, elements[elements.length - 1]));
		
		for (int i = elements.length - 2; 0 < i; --i) {
			result = list($(separator, elements[i], result));
		}
		
		result = list($(elements[0], result));
		
		return result;
	}
	
	/**
	 * @author codistmonk (creation 2016-08-12)
	 */
	public static final class PropositionDescription implements Serializable {
		
		private int index;
		
		private String name;
		
		private Object proposition;
		
		public final int getIndex() {
			return this.index;
		}
		
		public final PropositionDescription setIndex(final int index) {
			this.index = index;
			
			return this;
		}
		
		public final String getName() {
			return this.name;
		}
		
		public final PropositionDescription setName(final String name) {
			this.name = name;
			
			return this;
		}
		
		public final Object getProposition() {
			return this.proposition;
		}
		
		public final PropositionDescription setProposition(final Object proposition) {
			this.proposition = proposition;
			
			return this;
		}
		
		@Override
		public final String toString() {
			return this.getIndex() + ": " + this.getName() + ": " + this.getProposition();
		}
		
		private static final long serialVersionUID = -3590873676651429520L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-19)
	 */
	public static final class CaseDescription implements Serializable {
		
		private final Map<String, Object> variables;
		
		private final List<Object> conditions;
		
		private final Object definition;
		
		public CaseDescription(final Map<String, Object> variables, final List<Object> conditions, final Object definition) {
			this.variables = variables;
			this.conditions = conditions;
			this.definition = definition;
		}
		
		public final Map<String, Object> getVariables() {
			return this.variables;
		}
		
		public final List<Object> getConditions() {
			return this.conditions;
		}
		
		public final Object getDefinition() {
			return this.definition;
		}
		
		public final CaseDescription instantiate() {
			return this.instantiate("");
		}
		
		@SuppressWarnings("unchecked")
		public final CaseDescription instantiate(final String variableNamePostfix) {
			final Map<Variable, Object> map = new LinkedHashMap<>();
			final Map<String, Object> newVariables = new LinkedHashMap<>();
			
			for (final Map.Entry<String, ?> entry : this.getVariables().entrySet()) {
				final String newName = entry.getKey() + variableNamePostfix;
				final Object newValue = $new(newName);
				
				map.put((Variable) entry.getValue(), newValue);
				newVariables.put(newName, newValue);
			}
			
			return new CaseDescription(newVariables,
					(List<Object>) Variable.rewrite(this.getConditions(), map), Variable.rewrite(this.getDefinition(), map));
		}
		
		private static final long serialVersionUID = -9131355470296079371L;
		
	}
	
}
