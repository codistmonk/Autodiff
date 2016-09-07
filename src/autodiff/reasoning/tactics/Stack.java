package autodiff.reasoning.tactics;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.Substitution.equal;
import static multij.tools.Tools.last;
import static multij.tools.Tools.unchecked;

import autodiff.reasoning.expressions.ExpressionVisitor;
import autodiff.reasoning.proofs.Binding;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.ElementaryVerification;
import autodiff.reasoning.proofs.ModusPonens;
import autodiff.reasoning.proofs.Proof;
import autodiff.reasoning.proofs.Substitution;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.Collection;
import java.util.Iterator;
import java.util.List;
import java.util.Map;

import multij.tools.IllegalInstantiationException;
import multij.tools.Pair;

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
	
	public static final void popTo(final Deduction deduction) {
		while (deduction() != deduction) {
			pop();
		}
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
			final Map<Object, Object> replacements, final int... indices) {
		substitute(null, target, replacements, indices);
	}
	
	public static final void substitute(final String propositionName, final Object target,
			final Map<Object, Object> replacements, final int... indices) {
		conclude(new Substitution(propositionName, target, replacements, indices(indices)));
	}
	
	public static final void bind(final String targetName, final Object... values) {
		bind(newName(), targetName, values);
	}
	
	public static final void bind(final String propositionName, final String targetName, final Object... values) {
		subdeduction(propositionName);
		
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
	
	public static final void verifyElementaryProposition(final Object proposition) {
		verifyElementaryProposition(newName(), proposition);
	}
	
	public static final void verifyElementaryProposition(final String propositionName, final Object proposition) {
		conclude(new ElementaryVerification(propositionName, Arrays.asList("By elementary verification"), proposition));
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
		return deduction().checkProposition(name);
	}
	
	public static final List<Object> checkRule(final String name) {
		return deduction().checkRule(name);
	}
	
	public static final List<Object> checkEquality(final String name) {
		return checkEquality(name, deduction());
	}
	
	@SuppressWarnings("unchecked")
	public static final List<Object> checkEquality(final String name, final Deduction context) {
		final Object result = context.checkProposition(name);
		
		checkArgument(isEquality(result), "Not an equality: " + result);
		
		return (List<Object>) result;
	}
	
	public static final List<Object> checkSubstitution(final String name) {
		return checkSubstitution(name, deduction());
	}
	
	@SuppressWarnings("unchecked")
	public static final List<Object> checkSubstitution(final String name, final Deduction context) {
		final Object result = context.checkProposition(name);
		
		checkArgument(isSubstitution(result), "Not a substitution: " + result);
		
		return (List<Object>) result;
	}
	
	public static final List<Object> checkBlock(final String name) {
		return deduction().checkBlock(name);
	}
	
	public static final int countIn(final Object target, final Object pattern) {
		return new ExpressionVisitor<Integer>() {
			
			@Override
			public final Integer visit(final Object expression) {
				if (equal(pattern, expression)) {
					return 1;
				}
				
				return 0;
			}
			
			@Override
			public final Integer visit(final List<?> expression) {
				final Integer result = this.visit((Object) expression);
				
				return 0 < result ? result : expression.stream().mapToInt(this::apply).sum();
			}
			
			private static final long serialVersionUID = 2608876360859599240L;
			
		}.apply(target);
	}
	
	public static final void abort() {
		abort("Aborted");
	}
	
	public static final void abort(final String message) {
		throw new AbortException(message);
	}
	
	/**
	 * @author codistmonk (creation 2016-08-23)
	 */
	public static final class AbortException extends RuntimeException {
		
		public AbortException(final String message) {
			super(message);
		}
		
		public AbortException() {
			this("Aborted");
		}
		
		private static final long serialVersionUID = -3683176562496539944L;
		
	}
	
	/**
	 * @author codistmonk (creation 2016-08-12)
	 */
	public static final class PropositionDescription implements Serializable, Cloneable {
		
		private int index;
		
		private String name;
		
		private Object proposition;
		
		@Override
		public final PropositionDescription clone() {
			try {
				return (PropositionDescription) super.clone();
			} catch (final CloneNotSupportedException exception) {
				throw unchecked(exception);
			}
		}
		
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
		
		public static final PropositionDescription existingJustificationFor(final Object proposition) {
			for (final PropositionDescription description : iterateBackward(deduction())) {
				if (equal(proposition, description.getProposition())) {
					return description;
				}
			}
			
			return null;
		}
		
		public static final List<Pair<PropositionDescription, PatternMatching>> potentialJustificationsFor(final Object propositionPattern) {
			final List<Pair<PropositionDescription, PatternMatching>> result = new ArrayList<>();
			
			for (final PropositionDescription description : iterateBackward(deduction())) {
				Object target = description.getProposition();
				
				while (target != null) {
					final PatternMatching patternMatching = new PatternMatching();
					
					
					if (patternMatching.apply(propositionPattern, target)) {
						result.add(new Pair<>(description.clone(), patternMatching));
					}
					
					if (isRule(target)) {
						target = conclusion(target);
					} else if (isBlock(target)) {
						target = scope(target);
					} else {
						target = null;
					}
				}
			}
			
			return result;
		}
		
		public static final boolean isEmpty(final Deduction deduction) {
			return deduction == null
					|| (deduction.getPropositionNames().isEmpty()
							&& (deduction.getParent() == null || isEmpty(deduction.getParent())));
		}
		
	}
	
}
