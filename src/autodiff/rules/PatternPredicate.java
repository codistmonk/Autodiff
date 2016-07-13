package autodiff.rules;

import java.util.Map;

/**
 * @author codistmonk (creation 2016-07-13)
 */
public final class PatternPredicate implements SimpleRule.Predicate<Object> {
	
	private final Object pattern;
	
	public PatternPredicate(final Object pattern) {
		this.pattern = pattern;
	}
	
	@Override
	public final boolean test(final Object object, final Map<Variable, Object> mapping) {
		return Variable.match(this.pattern, object, mapping);
	}
	
	private static final long serialVersionUID = -5516068695919791749L;
	
	public static final <R> SimpleRule<Object, R> rule(final Object pattern, final SimpleRule.Application<Object, R> application) {
		return new SimpleRule<>(new PatternPredicate(pattern), application);
	}
	
}