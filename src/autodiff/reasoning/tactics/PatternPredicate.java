package autodiff.reasoning.tactics;

import java.util.Map;

import autodiff.rules.Application;
import autodiff.rules.Predicate;
import autodiff.rules.CompositeRule;
import autodiff.rules.Variable;

/**
 * @author codistmonk (creation 2016-08-16)
 */
public final class PatternPredicate implements Predicate<Object> {
	
	private final Object pattern;
	
	public PatternPredicate(final Object pattern) {
		this.pattern = pattern;
	}
	
	@Override
	public final boolean test(final Object object, final Map<Variable, Object> mapping) {
		return new PatternMatching(mapping).apply(this.pattern, object);
	}
	
	private static final long serialVersionUID = -5516068695919791749L;
	
	public static final <R> CompositeRule<Object, R> rule(final Object pattern, final Application<Object, R> application) {
		return new CompositeRule<>(new PatternPredicate(pattern), application);
	}
	
}