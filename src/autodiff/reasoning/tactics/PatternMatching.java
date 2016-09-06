package autodiff.reasoning.tactics;

import static multij.tools.Tools.cast;

import autodiff.reasoning.proofs.Substitution.AbstractExpressionEquality;
import autodiff.rules.Variable;

import java.util.LinkedHashMap;
import java.util.Map;

/**
 * @author codistmonk (creation 2016-08-16)
 */
public final class PatternMatching extends AbstractExpressionEquality {
	
	private final Map<Variable, Object> mapping;
	
	public PatternMatching() {
		this(new LinkedHashMap<>());
	}
	
	public PatternMatching(final Map<Variable, Object> mapping) {
		this.mapping = mapping;
	}
	
	public final Map<Variable, Object> getMapping() {
		return this.mapping;
	}
	
	@Override
	protected final boolean postVisit(final Object expression1, final Object expression2) {
		final Variable variable = cast(Variable.class, expression1);
		
		if (variable != null) {
			final Object existing = this.getMapping().get(variable);
			
			if (existing == null) {
				this.getMapping().put(variable, expression2);
				
				variable.set(expression2);
				
				return true;
			}
			
			return existing.equals(expression2);
		}
		
		return false;
	}
	
	private static final long serialVersionUID = 988081600699862962L;
	
	public static final boolean match(final Object pattern, final Object target) {
		return new PatternMatching().apply(pattern, target);
	}
	
	public static final void matchOrFail(final Object pattern, final Object target) {
		if (!match(pattern, target)) {
			throw new IllegalArgumentException("Failed to match " + pattern + " with " + target);
		}
	}
	
}