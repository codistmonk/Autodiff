package autodiff.reasoning.io;

import static autodiff.reasoning.expressions.Expressions.*;
import static java.util.Collections.nCopies;
import static java.util.stream.Collectors.toList;
import static multij.tools.Tools.*;
import autodiff.reasoning.expressions.Expressions;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.Proof;

import java.io.PrintStream;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import multij.tools.IllegalInstantiationException;
import multij.tools.Tools;

/**
 * @author codistmonk (creation 2015-04-12)
 */
public final class Simple {
	
	private Simple() {
		throw new IllegalInstantiationException();
	}
	
	private static Object groupStart = "(";
	
	private static Object groupEnd = ")";
	
	private static Object implies = Expressions.IMPLIES;
	
	public static final synchronized Object getGroupStart() {
		return groupStart;
	}
	
	public static final synchronized Object getGroupEnd() {
		return groupEnd;
	}
	
	public static final synchronized void setGroupStartEnd(final String groupStart, final String groupEnd) {
		Simple.groupStart = groupStart;
		Simple.groupEnd = groupEnd;
	}
	
	public static final synchronized Object getImplies() {
		return implies;
	}
	
	public static final synchronized void setImplies(final String implies) {
		Simple.implies = implies;
	}
	
	public static int print(final Deduction deduction, final int proofDepth) {
		return print(deduction, proofDepth, System.out);
	}
	
	public static int print(final Deduction deduction, final int proofDepth, final PrintStream output) {
		if (deduction == null) {
			return -1;
		}
		
		final int result = 1 + print(deduction.getParent(), 0, output);
		
		print(deduction, proofDepth, Tools.join("", nCopies(result, "\t")), output);
		
		return result;
	}
	
	public static final void print(final Deduction deduction, final int proofDepth, final String prefix, final PrintStream output) {
		final String tab = "\t";
		final String prefix1 = prefix + tab;
		final String prefix2 = prefix1 + tab;
		
		output.println(prefix + "((Deduction of " + deduction.getProvedPropositionName() + "))");
		
		{
			final Collection<Object> parameters = deduction.getParameters();
			
			if (!parameters.isEmpty()) {
				output.println(prefix1 + FORALL + parameters);
			}
		}
		
		{
			final List<String> conditionNames = deduction.getConditionNames();
			
			if (!conditionNames.isEmpty()) {
				output.println(prefix + "((Conditions))");
				
				for (final String conditionName : conditionNames) {
					output.println(prefix1 + conditionName + ":");
					output.println(prefix1 + collapse(deduction.getProposition(conditionName)));
				}
			}
		}
		
		{
			final List<String> conclusionNames = deduction.getConclusionNames();
			
			if (!conclusionNames.isEmpty()) {
				output.println(prefix + "((Conclusions))");
				
				for (final String conclusionName : conclusionNames) {
					output.println(prefix1 + conclusionName + ":");
					output.println(prefix1 + collapse(deduction.getProposition(conclusionName)));
					
					if (1 <= proofDepth) {
						final Proof proof = deduction.getProofs().get(conclusionName);
						
						if (1 == proofDepth || !(proof instanceof Deduction)) {
							output.println(prefix2 + collapse(proof.getMessage().stream().map(e -> e instanceof String ? " " + e + " " : collapse(e)).collect(toList())));
						} else {
							print((Deduction) proof, proofDepth - 1, prefix2, output);
						}
					}
				}
			}
		}
	}
	
	public static final String collapse(final Object object) {
		final Map<?, ?> map = cast(Map.class, object);
		
		if (map != null) {
			return Tools.join(",", iterable(
					map.entrySet().stream().map(e -> collapse(e.getKey()) + "=" + collapse(e.getValue()))));
		}
		
		final List<Object> expression = cast(List.class, object);
		
		if (expression == null) {
			return "" + object;
		}
		
		if (expression.isEmpty()) {
			return expression.toString();
		}
		
		if (isBlock(expression)) {
			return group(collapse(quantification(expression)) + " " + collapse(scope(expression)));
		}
		
		if (isRule(expression)) {
			return group(collapse(condition(expression)) + getImplies() + collapse(conclusion(expression)));
		}
		
		final String protoresult = Tools.join("", iterable(expression.stream().map(Simple::collapse)));
		
		if (isSubstitution(expression) || isEquality(expression)) {
			return group(protoresult);
		}
		
		return protoresult;
	}
	
	public static final synchronized String group(final Object object) {
		return "" + groupStart + object + groupEnd;
	}
	
}
