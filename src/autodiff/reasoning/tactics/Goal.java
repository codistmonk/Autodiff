package autodiff.reasoning.tactics;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.Substitution.compare;
import static autodiff.reasoning.tactics.Stack.*;

import autodiff.reasoning.proofs.Deduction;

import java.io.Serializable;
import java.util.HashMap;
import java.util.Map;

/**
 * @author codistmonk (creation 2015-04-12)
 */
public final class Goal implements Serializable {
	
	private final Object initialProposition;
	
	private Object proposition;
	
	private final Deduction deduction;
	
	public Goal(final Object proposition, final Deduction context, final String deductionName) {
		this.initialProposition = proposition;
		this.proposition = proposition;
		this.deduction = push(new Deduction(context, deductionName));
		
		activeGoals.put(this.getDeduction(), this);
	}
	
	public final Object getInitialProposition() {
		return this.initialProposition;
	}
	
	public final Object getProposition() {
		return this.proposition;
	}
	
	public final Deduction getDeduction() {
		return this.deduction;
	}
	
	public final Object introduce() {
		Object result = null;
		
		if (isBlock(this.getProposition())) {
			result = variable(this.getProposition());
			this.proposition = scope(this.getProposition());
			
			this.getDeduction().forall(result);
		} else if (isRule(this.getProposition())) {
			result = condition(this.getProposition());
			this.proposition = conclusion(this.getProposition());
			
			this.getDeduction().suppose(this.getDeduction().newPropositionName(), result);
		}
		
		return result;
	}
	
	public final void intros() {
		while (this.introduce() != null) {
			// NOP
		}
	}
	
	public final void conclude() {
		final Deduction deduction = this.getDeduction();
		
		if (pop() != deduction) {
			throw new IllegalStateException();
		}
		
		final Object provedProposition = deduction.getProvedPropositionFor(deduction.getParent());
		
		checkState(compare(this.getInitialProposition(), provedProposition),
				"Expected: " + this.getInitialProposition() + " but was: " + provedProposition);
		
		deduction().conclude(deduction);
		
		activeGoals.remove(deduction);
	}
	
	private static final long serialVersionUID = -6412523746037749196L;
	
	private static final Map<Deduction, Goal> activeGoals = new HashMap<>();
	
	public static final Goal activeGoalFor(final Deduction deduction) {
		return activeGoals.get(deduction);
	}
	
	public static final void concludeGoal() {
		goal().conclude();
	}
	
	public static final Goal goal() {
		Deduction deduction = deduction();
		Goal result = activeGoalFor(deduction);
		
		while (result == null) {
			deduction = deduction.getParent();
			result = activeGoalFor(deduction);
		}
		
		return result;
	}
	
	public static final Goal newGoal(final Object proposition) {
		return newGoal(newName(), proposition);
	}
	
	public static final Goal newGoal(final String propositionName, final Object proposition) {
		return new Goal(proposition, deduction(), propositionName);
	}
	
}