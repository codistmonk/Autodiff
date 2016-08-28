package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.rewrite;
import static autodiff.reasoning.deductions.Sets.ebindTrim;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.Stack.*;
import static autodiff.reasoning.tactics.PatternPredicate.rule;
import static multij.tools.Tools.append;
import static multij.tools.Tools.array;

import autodiff.reasoning.deductions.Sets.CaseDescription;
import autodiff.reasoning.tactics.Goal;
import autodiff.rules.Rules;
import autodiff.rules.Variable;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collections;
import java.util.List;
import java.util.Map;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-08-28)
 */
public final class Sequences {
	
	private Sequences() {
		throw new IllegalInstantiationException();
	}
	
	public static final void setup() {
//		debugPrint(sequence(",", $(1, 2, 3)));
//		debugPrint(sequence(",", 1));
//		debugPrint(sequence(",", 1, 2));
//		debugPrint(sequence(",", 1, 2, 3));
//		debugPrint(sequence(",", 1, sequence(",", 2, 3)));
//		debugPrint(sequence(",", sequence(",", 1, 2), 3));
//		debugPrint(sequence(",", 1, sequence(",", 2, 3), 4));
//		debugPrint(sequence(",", 1, 2, 3, 4));
		
		supposeDefinitionsForSequenceAppend();
		testSequenceAppend();
		
		supposeDefinitionsForSequenceConcatenate();
		testSequenceConcatenate();
		
		supposeEliminationsOfCases();
		testEliminationOfCases();
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
	
	public static void supposeEliminationsOfCases() {
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

	public static void testEliminationOfCases() {
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
		return sequence("", append(array((Object) "cases"), cases));
	}
	
	public static final CaseDescription newSequenceConcatenateCase0() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_x, "=", $()));
		final Object value = _y;
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"y", _y),
				conditions,
				$($("sequence_concatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceConcatenateCase1() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList($(_y, "=", $()));
		final Object value = _x;
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"y", _y),
				conditions,
				$($("sequence_concatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceConcatenateCase2() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _y = new Variable("y");
		final Object _y0 = new Variable("y0");
		
		final List<Object> conditions = Arrays.asList($(_y, "=", $1(_y0)));
		final Object value = $("sequence_append", _s, _x, _y0);
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"y", _y,
						"y0", _y0),
				conditions,
				$($("sequence_concatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceConcatenateCase3() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _y = new Variable("y");
		final Object _y0 = new Variable("y0");
		final Object _y1 = new Variable("y1");
		
		final List<Object> conditions = Arrays.asList(
				$(_x, "=", $1(_x0)),
				$(_y, "=", $(_y0, _y1)));
		final Object value = $(_x0, $(_s, _y0, _y1));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"y", _y,
						"y0", _y0,
						"y1", _y1),
				conditions,
				$($("sequence_concatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceConcatenateCase4() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _x1 = new Variable("x1");
		final Object _y = new Variable("y");
		final Object _y0 = new Variable("y0");
		final Object _y1 = new Variable("y1");
		
		final List<Object> conditions = Arrays.asList(
				$(_x, "=", $(_x0, _x1)),
				$(_y, "=", $(_y0, _y1)));
		final Object value = $(_x0, $("sequence_subconcatenate", _s, _x1, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"x1", _x1,
						"y", _y,
						"y0", _y0,
						"y1", _y1),
				conditions,
				$($("sequence_concatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceSubconcatenateCase0() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _y = new Variable("y");
		final Object _y0 = new Variable("y0");
		final Object _y1 = new Variable("y1");
		
		final List<Object> conditions = Arrays.asList(
				$(_x, "=", $(_s, _x0)),
				$(_y, "=", $(_y0, _y1)));
		final Object value = $(_s, _x0, $(_s, _y0, _y1));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"y", _y,
						"y0", _y0,
						"y1", _y1),
				conditions,
				$($("sequence_subconcatenate", _s, _x, _y), "=", value));
	}
	
	public static final CaseDescription newSequenceSubconcatenateCase1() {
		final Object _s = new Variable("s");
		final Object _x = new Variable("x");
		final Object _x0 = new Variable("x0");
		final Object _x1 = new Variable("x1");
		final Object _y = new Variable("y");
		
		final List<Object> conditions = Arrays.asList(
				$(_x, "=", $(_s, _x0, _x1)));
		final Object value = $(_s, _x0, $("sequence_subconcatenate", _s, _x1, _y));
		
		return new CaseDescription(
				map(
						"s", _s,
						"x", _x,
						"x0", _x0,
						"x1", _x1,
						"y", _y),
				conditions,
				$($("sequence_subconcatenate", _s, _x, _y), "=", value));
	}
	
	public static final void supposeDefinitionsForSequenceConcatenate() {
		/*
		 * 
		 * 0: concatenate s [] y            = y
		 * 1: concatenate s x []            = x
		 * 2: concatenate s x [y0]          = append s x y0
		 * 3: concatenate s [x0] [y0 y1]    = [x0 [s y0 y1]]
		 * 4: concatenate s [x0 x1] [y0 y1] = [x0 (subconcatenate s x1 y)]
		 * 
		 * 0: subconcatenate s [s x0] [y0 y1] = [s x0 [s y0 y1]] 
		 * 1: subconcatenate s [s x0 x1] y = [s x0 (subconcatenate s x1 y)] 
		 * 
		 */
		
		supposeDefinitions("sequence_concatenate",
				newSequenceConcatenateCase0(),
				newSequenceConcatenateCase1(),
				newSequenceConcatenateCase2(),
				newSequenceConcatenateCase3(),
				newSequenceConcatenateCase4());
		
		supposeDefinitions("sequence_subconcatenate",
				newSequenceSubconcatenateCase0(),
				newSequenceSubconcatenateCase1());
	}
	
	public static final void testSequenceConcatenate() {
		final Object _s = $(",");
		
		{
			final Object _x = sequence(_s);
			final Object _y = sequence(_s);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.newGoal("sequence_concatenate.test1",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
		
		{
			final Object _x = sequence(_s);
			final Object _y = sequence(_s, 1);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.newGoal("sequence_concatenate.test2",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
		
		{
			final Object _x = sequence(_s, 1);
			final Object _y = sequence(_s);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.newGoal("sequence_concatenate.test3",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
		
		{
			final Object _x = sequence(_s, 1);
			final Object _y = sequence(_s, 2);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.newGoal("sequence_concatenate.test4",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
		
		{
			final Object _x = sequence(_s, 1, 2);
			final Object _y = sequence(_s, 3);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.newGoal("sequence_concatenate.test5",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
		
		{
			final Object _x = sequence(_s, 1, 2, 3);
			final Object _y = sequence(_s, 4, 5, 6);
			
			{
				final Object expectedValue = sequence(_s, append(flattenSequence(_s, _x).toArray(), flattenSequence(_s, _y).toArray()));
				final Goal goal = Goal.newGoal("sequence_concatenate.test6",
						$($("sequence_concatenate", _s, _x, _y), "=", expectedValue));
				
				computeSequenceConcatenate(_s, _x, _y);
				
				goal.conclude();
			}
		}
	}
	
	public static final void computeSequenceConcatenate(final Object s, final Object x, final Object y) {
		computeSequenceConcatenate(newName(), s, x, y);
	}
	
	public static final void computeSequenceConcatenate(final String propositionName, final Object s, final Object x, final Object y) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final CaseDescription c = newSequenceConcatenateCase0();
			final Map<String, Object> v = c.getVariables();
			
			final Object _s = v.get("s");
			final Object _y = v.get("y");
			
			rules.add(rule($(_s, first(c.getConditions()), $(_y, "=", _y)), (__, m) -> {
				ebindTrim("definition_of_sequence_concatenate_0", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceConcatenateCase1();
			final Map<String, Object> v = c.getVariables();
			
			final Object _s = v.get("s");
			final Object _x = v.get("x");
			
			rules.add(rule($(_s, $(_x, "=", _x), first(c.getConditions())), (__, m) -> {
				ebindTrim("definition_of_sequence_concatenate_1", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceConcatenateCase2();
			final Map<String, Object> v = c.getVariables();
			
			final Object _s = v.get("s");
			final Object _x = v.get("x");
			final Object _y0 = v.get("y0");
			
			rules.add(rule($(_s, $(_x, "=", _x), first(c.getConditions())), (__, m) -> {
				{
					subdeduction();
					
					ebindTrim("definition_of_sequence_concatenate_2", v.values().stream().map(m::get).toArray());
					computeSequenceAppend(m.get(_s), m.get(_x), m.get(_y0));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceConcatenateCase3();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), first(c.getConditions()), second(c.getConditions())), (__, m) -> {
				ebindTrim("definition_of_sequence_concatenate_3", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceConcatenateCase4();
			final Map<String, Object> v = c.getVariables();
			
			final Object _s = v.get("s");
			final Object _x1 = v.get("x1");
			final Object _y = v.get("y");
			
			rules.add(rule($(_s, first(c.getConditions()), second(c.getConditions())), (__, m) -> {
				{
					subdeduction();
					
					ebindTrim("definition_of_sequence_concatenate_4", v.values().stream().map(m::get).toArray());
					computeSequenceSubconcatenate(m.get(_s), m.get(_x1), m.get(_y));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		{
			subdeduction(propositionName);
			
			rules.applyTo($(s, $(x, "=", x), $(y, "=", y)));
			
			conclude();
		}
	}
	
	public static final void computeSequenceSubconcatenate(final Object s, final Object x, final Object y) {
		computeSequenceSubconcatenate(newName(), s, x, y);
	}
	
	public static final void computeSequenceSubconcatenate(final String propositionName, final Object s, final Object x, final Object y) {
		final Rules<Object, Void> rules = new Rules<>();
		
		{
			final CaseDescription c = newSequenceSubconcatenateCase0();
			final Map<String, Object> v = c.getVariables();
			
			rules.add(rule($(v.get("s"), first(c.getConditions()), second(c.getConditions())), (__, m) -> {
				ebindTrim("definition_of_sequence_subconcatenate_0", v.values().stream().map(m::get).toArray());
				
				return null;
			}));
		}
		
		{
			final CaseDescription c = newSequenceSubconcatenateCase1();
			final Map<String, Object> v = c.getVariables();
			final Object _s = v.get("s");
			final Object _x1 = v.get("x1");
			final Object _y = v.get("y");
			
			rules.add(rule($(_s, first(c.getConditions()), $(_y, "=", _y)), (__, m) -> {
				{
					subdeduction();
					
					ebindTrim("definition_of_sequence_subconcatenate_1", v.values().stream().map(m::get).toArray());
					computeSequenceSubconcatenate(m.get(_s), m.get(_x1), m.get(_y));
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				return null;
			}));
		}
		
		{
			subdeduction(propositionName);
			
			rules.applyTo($(s, $(x, "=", x), $(y, "=", y)));
			
			conclude();
		}
	}
	
}
