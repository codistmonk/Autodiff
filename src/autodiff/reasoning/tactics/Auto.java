package autodiff.reasoning.tactics;

import static autodiff.reasoning.deductions.Basics.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.tactics.Stack.*;
import static multij.tools.Tools.ignore;

import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.tactics.Stack.AbortException;
import autodiff.rules.Rule;
import autodiff.rules.Rules;
import autodiff.rules.Variable;

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
	
	private static final Map<Deduction, Rules<Object, Void>> rules = new WeakHashMap<>();
	
	public static final void addRule(final Rule<Object, Void> rule) {
		rules.computeIfAbsent(deduction(), __ -> new Rules<>()).add(rule);
	}
	
	public static final void autodeduce(final Object proposition) {
		final Deduction deduction = subdeduction();
		
		{
			final PropositionDescription justification = PropositionDescription.existingJustificationFor(proposition);
			
			if (justification != null) {
				recall(justification.getName());
				
				conclude();
				
				return;
			}
		}
		
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
						rules.get(d).applyTo(proposition);
						
						conclude();
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
		String lastName = targetName;
		
		for (final Object object : objects) {
			
			final Variable vX = new Variable("X");
			final Variable vP = new Variable("P");
			
			autodeduce($(proposition(lastName), "=", $forall(vX, vP)));
			rewrite(lastName, name(-1));
			bind(name(-1), object);
		}
	}
	
	public static final void autoapply(final String targetName) {
		subdeduction();
		
		final Variable vX = new Variable("X");
		final Variable vY = new Variable("Y");
		final Object pattern = $rule(vX, vY);
		String currentTargetName = targetName;
		boolean concludeNeeded = false;
		
		while (Variable.match(pattern, currentTargetName)) {
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
	
}
