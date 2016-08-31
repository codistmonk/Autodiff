package autodiff.reasoning.tactics;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.tools.Tools.ignore;

import autodiff.reasoning.expressions.ExpressionRewriter;
import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.tactics.Stack.AbortException;
import autodiff.reasoning.tactics.Stack.PropositionDescription;
import autodiff.rules.Rule;
import autodiff.rules.Rules;
import autodiff.rules.SimpleRule;
import autodiff.rules.TryRule;
import autodiff.rules.Variable;

import java.util.HashMap;
import java.util.List;
import java.util.Map;
import java.util.WeakHashMap;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-08-28)
 */
public final class Auto {
	
	private Auto() {
		throw new IllegalInstantiationException();
	}
	
	private static final Map<Deduction, Rules<Object, Void>> autodeduceRules = new WeakHashMap<>();
	
	private static final Map<Deduction, Rules<Object, Void>> autobindRules = new WeakHashMap<>();
	
	public static final void hintAutodeduce(final TryRule<Object> rule) {
		autodeduceRules.computeIfAbsent(deduction(), __ -> new Rules<>()).add(rule);
	}
	
	public static final void hintAutobind(final Rule<Object, Void> rule) {
		autobindRules.computeIfAbsent(deduction(), __ -> new Rules<>()).add(rule);
	}
	
	public static final void autodeduce(final Object proposition) {
		autodeduce(newName(), proposition);
	}
	
	public static final void autodeduce(final String propositionName, final Object proposition) {
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
	}
	
	public static final void autobind(final String targetName, final Object... objects) {
		autobind(newName(), targetName, objects);
	}
	
	public static final void autobind(final String propositionName, final String targetName, final Object... objects) {
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
			
			final Variable vX = new Variable("X");
			final Variable vP = new Variable("P");
			final List<Object> pattern = $forall(vX, vP);
			
			if (new PatternMatching().apply(pattern, proposition(lastName))) {
				bind(lastName, object);
			} else {
				for (Deduction d = deduction(); d != null; d = d.getParent()) {
					try {
						autobindRules.get(d).applyTo(proposition(lastName));
						rewrite(lastName, name(-1));
						bind(name(-1), object);
					} catch (final AbortException exception2) {
						throw exception2;
					} catch (final Exception exception2) {
						ignore(exception2);
						
						popTo(deduction);
					}
				}
			}
			
			lastName = name(-1);
		}
		
		conclude();
	}
	
	public static final Object patternify(final Object object) {
		return new ExpressionRewriter() {
			
			private final Map<Object, Variable> variables = new HashMap<>();
			
			@Override
			public final Object visit(final Object expression) {
				return this.variables.computeIfAbsent(expression, __ -> new Variable());
			}
			
			private static final long serialVersionUID = -1327184193528204097L;
			
		}.apply(object);
	}
	
	public static final void autoapply(final String targetName) {
		autoapply(newName(), targetName);
	}
	
	public static final void autoapply(final String propositionName, final String targetName) {
		subdeduction(propositionName);
		
		final Variable vX = new Variable("X");
		final Variable vY = new Variable("Y");
		final Object pattern = $rule(vX, vY);
		String currentTargetName = targetName;
		boolean concludeNeeded = false;
		
		while (new PatternMatching().apply(pattern, proposition(currentTargetName))) {
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
		final Variable vX = new Variable("X");
		final Variable vY = new Variable("Y");
		final Object pattern = $rule(vX, vY);
		
		if (!new PatternMatching().apply(pattern, proposition(targetName))) {
			throw new IllegalArgumentException();
		}
		
		subdeduction(propositionName);
		
		autodeduce(vX.get());
		apply(targetName, name(-1));
		
		conclude();
	}
	
	public static final <T> TryRule<T> matchWith(final Object pattern, SimpleRule.Predicate<T> predicateContinuation) {
		return (e, m) -> new PatternMatching().apply(pattern, e)
					&& predicateContinuation.test(e, m);
	}
	
}
