package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;
import static multij.tools.Tools.last;

import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.List;
import java.util.Map;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2015-04-11)
 */
public final class Stack {
	
	private Stack() {
		throw new IllegalInstantiationException();
	}
	
	private static final List<Deduction> stack = new ArrayList<>();
	
	private static final List<Deduction> stack() {
		return stack;
	}
	
	public static final Deduction push() {
		return push("");
	}
	
	public static final Deduction push(final String deductionName) {
		return push(new Deduction(null, deductionName));
	}
	
	public static final Deduction push(final Deduction result) {
		stack().add(result);
		
		return result;
	}
	
	public static final Deduction pop() {
		return stack().remove(stack().size() - 1);
	}
	
	public static final Deduction pop(final Deduction deduction) {
		while (deduction != pop()) {
			// NOP;
		}
		
		return deduction;
	}
	
	public static final Deduction deduction() {
		return last(stack());
	}
	
	public static final Object forall(final String name) {
		final Object result = $new(name);
		
		deduction().forall(result);
		
		return result;
	}
	
	public static final void suppose(final Object proposition) {
		suppose(newName(), proposition);
	}
	
	public static final void suppose(final String propositionName, final Object proposition) {
		deduction().suppose(propositionName, proposition);
	}
	
	public static final void apply(final String ruleName, final String conditionName) {
		apply(null, ruleName, conditionName);
	}
	
	public static final void apply(final String propositionName, final String ruleName, final String conditionName) {
		conclude(new ModusPonens(propositionName, ruleName, conditionName));
	}
	
	public static final void substitute(final Object target,
			final Map<Object, Object> equalities, final int... indices) {
		substitute(null, target, equalities, indices);
	}
	
	public static final void substitute(final String propositionName, final Object target,
			final Map<Object, Object> equalities, final int... indices) {
		conclude(new Substitution(propositionName, target, equalities, indices(indices)));
	}
	
	public static final void bind(final String targetName, final Object... values) {
		subdeduction();
		
		final int n = values.length;
		
		bind(targetName, values[0]);
		
		for (int i = 1; i < n; ++i) {
			bind(name(-1), values[i]);
		}
		
		set(conclude().getMessage(), "By binding", targetName, "with", Arrays.asList(values));
	}
	
	public static final <T, C extends Collection<T>> C set(final C collection, @SuppressWarnings("unchecked") final T... elements) {
		collection.clear();
		collection.addAll(Arrays.asList(elements));
		
		return collection;
	}
	
	public static final void bind(final String targetName, final Object value) {
		bind(null, targetName, value);
	}
	
	public static final void bind(final String propositionName, final String targetName, final Object value) {
		conclude(new Binding(propositionName, targetName, value));
	}
	
	public static final void verifyBasicNumericProposition(final Object proposition) {
		verifyBasicNumericProposition(newName(), proposition);
	}
	
	public static final void verifyBasicNumericProposition(final String propositionName, final Object proposition) {
		conclude(new BasicNumericVerification(propositionName, Arrays.asList("By basic numeric verification"), proposition));
	}
	
	public static final Deduction subdeduction() {
		return subdeduction(newName());
	}
	
	public static final Deduction subdeduction(final String propositionName) {
		return push(new Deduction(deduction(), propositionName));
	}
	
	public static final Deduction conclude() {
		return conclude(pop());
	}
	
	public static final <P extends Proof> P conclude(final P proof) {
		deduction().conclude(proof);
		
		return proof;
	}
	
	public static final String name(final int index) {
		return deduction().getPropositionName(index);
	}
	
	public static final Object proposition(final String name) {
		return deduction().getProposition(name);
	}
	
	public static final Object proposition(final int index) {
		return deduction().getProposition(name(index));
	}
	
	public static final String newName() {
		return deduction().newPropositionName();
	}
	
	public static final Object checkProposition(final String name) {
		return checkProposition(name, deduction());
	}
	
	public static final Object checkProposition(final String name, final Deduction context) {
		final Object result = context.getProposition(name);
		
		checkArgument(result != null, "Missing proposition: " + name);
		
		return result;
	}
	
	public static final List<Object> checkRule(final String name) {
		return checkRule(name, deduction());
	}
	
	@SuppressWarnings("unchecked")
	public static final List<Object> checkRule(final String name, final Deduction context) {
		final Object result = checkProposition(name, context);
		
		checkArgument(isRule(result), "Not a rule: " + result);
		
		return (List<Object>) result;
	}
	
	public static final List<Object> checkEquality(final String name) {
		return checkEquality(name, deduction());
	}
	
	@SuppressWarnings("unchecked")
	public static final List<Object> checkEquality(final String name, final Deduction context) {
		final Object result = checkProposition(name, context);
		
		checkArgument(isEquality(result), "Not an equality: " + result);
		
		return (List<Object>) result;
	}
	
	public static final List<Object> checkSubstitution(final String name) {
		return checkSubstitution(name, deduction());
	}
	
	@SuppressWarnings("unchecked")
	public static final List<Object> checkSubstitution(final String name, final Deduction context) {
		final Object result = checkProposition(name, context);
		
		checkArgument(isSubstitution(result), "Not a substitution: " + result);
		
		return (List<Object>) result;
	}
	
	public static final List<Object> checkBlock(final String name) {
		return checkBlock(name, deduction());
	}
	
	@SuppressWarnings("unchecked")
	public static final List<Object> checkBlock(final String name, final Deduction context) {
		final Object result = checkProposition(name, context);
		
		checkArgument(isBlock(result), "Not a block: " + result);
		
		return (List<Object>) result;
	}
	
	public static final void abort() {
		throw new RuntimeException("Aborted");
	}
	
}
