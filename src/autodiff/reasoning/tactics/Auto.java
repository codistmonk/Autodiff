package autodiff.reasoning.tactics;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.PatternMatching.match;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.tools.Tools.*;

import autodiff.reasoning.expressions.ExpressionVisitor;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.tactics.Stack.AbortException;
import autodiff.reasoning.tactics.Stack.PropositionDescription;

import java.util.Arrays;
import java.util.Collection;
import java.util.HashSet;
import java.util.List;
import java.util.Map;
import java.util.TreeSet;
import java.util.WeakHashMap;

import multij.rules.Predicate;
import multij.rules.Rules;
import multij.rules.Rules.Result;
import multij.rules.TryRule;
import multij.rules.Variable;
import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-08-28)
 */
public final class Auto {
	
	private Auto() {
		throw new IllegalInstantiationException();
	}
	
	private static final Map<Deduction, Rules<Object, Boolean>> autodeduceRules = new WeakHashMap<>();
	
	private static final Map<Deduction, Rules<Object, Boolean>> autobindRules = new WeakHashMap<>();
	
	private static final Collection<Object> pending = new HashSet<>();
	
	public static final void hintAutodeduce(final TryRule<Object> rule) {
		autodeduceRules.computeIfAbsent(deduction(), __ -> new Rules<>()).add(rule);
	}
	
	public static final void hintAutobind(final TryRule<Object> rule) {
		autobindRules.computeIfAbsent(deduction(), __ -> new Rules<>()).add(rule);
	}
	
	public static final void autodeduce(final Object proposition) {
		autodeduce(newName(), proposition);
	}
	
	public static final void autodeduce(final String propositionName, final Object proposition) {
		checkState(pending.add(proposition), "Loop detected trying to autodeduce " + proposition);
		
		try {
			{
				final PropositionDescription justification = PropositionDescription.existingJustificationFor(proposition);
				
				if (justification != null) {
					recall(propositionName, justification.getName());
					
					return;
				}
			}
			
			final Deduction deduction = subdeduction(propositionName);
			
			try {
				try {
					verifyElementaryProposition(proposition);
					
					conclude();
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					popTo(deduction);
					
					for (Deduction d = deduction(); d != null; d = d.getParent()) {
						try {
							autodeduceRules.get(d).applyTo(proposition);
							
							conclude();
							
							return;
						} catch (final AbortException exception2) {
							throw exception2;
						} catch (final Exception exception2) {
							ignore(exception2);
							
							popTo(deduction);
						}
					}
					
					throw exception;
				}
			} catch (final AbortException exception) {
				throw exception;
			} catch (final Exception exception) {
				popTo(deduction.getParent());
				
				throw exception;
			}
		} finally {
			pending.remove(proposition);
		}
	}
	
	public static final void autobindTrim(final String targetName, final Object... objects) {
		autobindTrim(newName(), targetName, objects);
	}
	
	public static final void autobindTrim(final String propositionName, final String targetName, final Object... objects) {
		subdeduction(propositionName);
		
		autobind(targetName, objects);
		trim();
		
		conclude();
	}
	
	public static final void autobind(final String targetName, final Object... objects) {
		autobind(newName(), targetName, objects);
	}
	
	public static final void autobind(final String propositionName, final String targetName, final Object... objects) {
		if (proposition(targetName) == null) {
			abort("Missing proposition: " + targetName);
		}
		
		final Deduction deduction = subdeduction(propositionName);
		
		String lastName = targetName;
		
		for (final Object object : objects) {
			{
				final String tmp = name(-1);
				
				autoapply(lastName);
				
				if (!tmp.equals(name(-1))) {
					lastName = name(-1);
				}
			}
			
			final Variable vX = v("X");
			final Variable vP = v("P");
			final List<Object> pattern = $forall(vX, vP);
			
			if (match(pattern, proposition(lastName))) {
				bind(lastName, object);
			} else {
				boolean ok = false;
				
				for (Deduction d = deduction(); d != null; d = d.getParent()) {
					try {
						autobindRules.get(d).applyTo(proposition(lastName));
						rewrite(lastName, name(-1));
						bind(name(-1), object);
						ok = true;
					} catch (final AbortException exception2) {
						throw exception2;
					} catch (final Exception exception2) {
						ignore(exception2);
						
						popTo(deduction);
					}
				}
				
				if (!ok) {
					abort();
				}
			}
			
			lastName = name(-1);
		}
		
		conclude();
	}
	
	public static final void trim() {
		autoapply(name(-1));
	}
	
	public static final void autoapply(final String targetName) {
		autoapply(newName(), targetName);
	}
	
	public static final void autoapply(final String propositionName, final String targetName) {
		subdeduction(propositionName);
		
		final Variable vX = v("X");
		final Variable vY = v("Y");
		final Object pattern = $rule(vX, vY);
		String currentTargetName = targetName;
		boolean concludeNeeded = false;
		
		while (match(pattern, proposition(currentTargetName))) {
			autodeduce(vX.get());
			apply(currentTargetName, name(-1));
			currentTargetName = name(-1);
			concludeNeeded = true;
		}
		
		if (concludeNeeded) {
			conclude();
		} else {
			pop();
		}
	}
	
	public static final void autoapplyOnce(final String targetName) {
		autoapplyOnce(newName(), targetName);
	}
	
	public static final void autoapplyOnce(final String propositionName, final String targetName) {
		final Variable vX = v("X");
		final Variable vY = v("Y");
		final Object pattern = $rule(vX, vY);
		
		if (!match(pattern, proposition(targetName))) {
			throw new IllegalArgumentException();
		}
		
		subdeduction(propositionName);
		
		autodeduce(vX.get());
		apply(targetName, name(-1));
		
		conclude();
	}
	
	public static final <T> TryRule<T> tryMatch(final Object pattern, Predicate<T> continuation) {
		return new TryRule<T>() {
			
			@Override
			public final Result<Boolean> apply(final T e, final Map<Variable, Object> m) {
				final Deduction deduction = deduction();
				
				try {
					if (new PatternMatching(m).apply(pattern, e)
						&& continuation.test(e, m)) {
						return T;
					}
				} catch (final AbortException exception) {
					throw exception;
				} catch (final Exception exception) {
					ignore(exception);
					
					popTo(deduction);
				}
				
				return null;
			}
						
			private static final long serialVersionUID = 5597439472888754461L;
			
		};
	}
	
	public static final Variable v() {
		return v("?");
	}
	
	public static final Variable v(final String name) {
		return new Variable(name);
	}
	
	/**
	 * @author codistmonk (creation 2016-08-21)
	 */
	public static final class Simplifier implements ExpressionVisitor<Boolean> {
		
		private final Rules<Object, Boolean> rules;
		
		private final Collection<Integer> indices;
		
		private final Mode mode;
		
		private final Traversal traversal;
		
		private int currentIndex;
		
		public Simplifier() {
			this(Mode.REWRITE, Traversal.PREFIX);
		}
		
		public Simplifier(final Mode mode) {
			this(mode, Traversal.PREFIX);
		}
		
		public Simplifier(final Mode mode, final Traversal traversal) {
			this.rules = new Rules<>();
			this.indices = new TreeSet<>();
			this.mode = mode;
			this.traversal = traversal;
		}
		
		public final Collection<Integer> getIndices() {
			return this.indices;
		}
		
		public final Simplifier setIndices(final Integer... indices) {
			this.getIndices().clear();
			this.getIndices().addAll(Arrays.asList(indices));
			
			return this;
		}
		
		public final int getCurrentIndex() {
			return this.currentIndex;
		}
		
		public final Rules<Object, Boolean> getRules() {
			return this.rules;
		}
		
		public final Mode getMode() {
			return this.mode;
		}
		
		public final Traversal getTraversal() {
			return this.traversal;
		}
		
		public final Simplifier add(final TryRule<Object> rule) {
			this.getRules().add(rule);
			
			return this;
		}
		
		public final void simplifyCompletely(final Object expression) {
			subdeduction();
			
			if (this.apply(this.isDefining() ? right(expression) : expression)) {
				while (this.apply(this.isDefining() ? right(proposition(-1)) : proposition(-1))) {
					// NOP
				}
				
				conclude();
			} else {
				pop();
			}
		}
		
		@Override
		public final Boolean visit(final Object expression) {
			return this.tryRules(expression);
		}
		
		@Override
		public final Boolean visit(final List<?> expression) {
			if (Traversal.PREFIX.equals(this.getTraversal()) && this.tryRules(expression)) {
				return true;
			}
			
			for (final Object subExpression : expression) {
				if (this.apply(subExpression)) {
					return true;
				}
			}
			
			if (Traversal.POSTFIX.equals(this.getTraversal()) && this.tryRules(expression)) {
				return true;
			}
			
			return false;
		}
		
		private final boolean tryRules(final Object expression) {
			final Deduction deduction = subdeduction();
			
			try {
				if (this.getRules().applyTo(expression)) {
					if (this.isDefining()) {
						final int targets = countIn(proposition(-2), left(proposition(-1)));
						final int leftTargets = countIn(left(proposition(-2)), left(proposition(-1)));
						
						if (leftTargets < targets) {
							final int[] rightTargets = new int[targets - leftTargets];
							
							for (int i = leftTargets; i < targets; ++i) {
								rightTargets[i - leftTargets] = i;
							}
							
							rewrite(name(-2), name(-1), rightTargets);
						} else {
							popTo(deduction.getParent());
							
							return false;
						}
					} else {
						rewrite(name(-2), name(-1));
					}
					
					if (!this.getIndices().isEmpty() && !this.getIndices().contains(this.currentIndex)) {
						pop();
					} else {
						conclude();
					}
					
					++this.currentIndex;
					
					return true;
				}
			} catch (final AbortException exception) {
				throw exception;
			} catch (final Exception exception) {
				ignore(exception);
			}
			
			popTo(deduction.getParent());
			
			return false;
		}
		
		private final boolean isDefining() {
			return Mode.DEFINE.equals(this.getMode());
		}
		
		private static final long serialVersionUID = -5429351197907942483L;
		
		/**
		 * @author codistmonk (creation 2016-08-23)
		 */
		public static enum Mode {
			
			REWRITE, DEFINE;
			
		}
		
		/**
		 * @author codistmonk (creation 2016-09-08)
		 */
		public static enum Traversal {
			
			PREFIX, POSTFIX;
			
		}
		
	}
	
}
