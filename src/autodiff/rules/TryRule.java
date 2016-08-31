package autodiff.rules;

import static multij.tools.Tools.ignore;

import java.util.Map;

/**
 * @author codistmonk (creation 2016-08-31)
 */
public interface TryRule<T> extends Rule<T, Void> {
	
	@Override
	public default Void applyTo(final T object, final Map<Variable, Object> mapping) {
		ignore(object);
		ignore(mapping);
		
		return null;
	}
	
}
