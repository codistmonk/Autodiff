package autodiff.rules;

import autodiff.rules.Rules.Result;

/**
 * @author codistmonk (creation 2016-08-31)
 */
public abstract interface TryRule<T> extends Rule<T, Boolean> {
	
	public static final Result<Boolean> T = new Result<>(true);
	
	public static final Result<Boolean> F = new Result<>(false);
	
}
