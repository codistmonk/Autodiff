package autodiff.rules;

/**
 * @author codistmonk (creation 2015-12-07)
 *
 * @param <T>
 * @param <R>
 */
public abstract interface Rule<T, R> extends Application<T, Rules.Result<R>> {
	// Deliberately left empty
}