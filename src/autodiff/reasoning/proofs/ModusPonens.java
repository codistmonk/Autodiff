package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.Stack.*;

import java.util.Arrays;
import java.util.List;

/**
 * @author codistmonk (creation 2015-04-11)
 */
public final class ModusPonens extends Proof.Abstract {
	
	private final String ruleName;
	
	private final String conditionName;
	
	public ModusPonens(final String ruleName, final String conditionName) {
		this(null, ruleName, conditionName);
	}
	
	public ModusPonens(final String provedPropositionName, final String ruleName, final String conditionName) {
		super(provedPropositionName, Arrays.asList("By applying", ruleName, "on", conditionName));
		this.ruleName = ruleName;
		this.conditionName = conditionName;
	}
	
	public final String getRuleName() {
		return this.ruleName;
	}
	
	public final String getConditionName() {
		return this.conditionName;
	}
	
	@Override
	public final Object getProvedPropositionFor(final Deduction context) {
		final List<Object> rule = list(checkRule(this.getRuleName(), context));
		final Object expectedCondition = condition(rule);
		final Object condition = checkProposition(this.getConditionName(), context);
		
		checkArgument(new Substitution.ExpressionEquality().apply(expectedCondition, condition), "Expected condition: " + expectedCondition + " but was: " + condition);
		
		return rule.get(2);
	}
	
	private static final long serialVersionUID = 8564800788237315329L;
	
}