package autodiff.reasoning.deductions;

import static autodiff.reasoning.deductions.Basics.rewrite;
import static autodiff.reasoning.deductions.Sets.ebindTrim;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.Stack.*;
import static autodiff.reasoning.tactics.PatternPredicate.rule;
import static multij.tools.Tools.append;

import autodiff.reasoning.deductions.Sets.CaseDescription;
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
		supposeDefinitionsForSequenceAppend();
		testSequenceAppend();
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
	
}
