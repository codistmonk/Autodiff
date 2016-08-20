package autodiff.reasoning.tactics;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.Stack.*;

import autodiff.reasoning.proofs.Deduction;

import java.io.Serializable;

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
		
		checkState(this.getInitialProposition().equals(provedProposition),
				"Expected: " + this.getInitialProposition() + " but was: " + provedProposition);
		
		deduction().conclude(deduction);
	}
	
	private static final long serialVersionUID = -6412523746037749196L;
	
	public static final Goal deduce(final Object proposition) {
		return deduce(newName(), proposition);
	}
	
	public static final Goal deduce(final String propositionName, final Object proposition) {
		return new Goal(proposition, deduction(), propositionName);
	}
	
}