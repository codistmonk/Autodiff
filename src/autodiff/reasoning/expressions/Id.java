package autodiff.reasoning.expressions;

import java.io.Serializable;

/**
 * @author codistmonk (creation 2015-04-11)
 */
public final class Id implements Serializable, CharSequence {
	
	private final CharSequence string;
	
	public Id(final CharSequence string) {
		this.string = string;
	}
	
	@Override
	public final String toString() {
		return this.string.toString();
	}
	
	@Override
	public final int length() {
		return this.toString().length();
	}
	
	@Override
	public final char charAt(final int index) {
		return this.toString().charAt(index);
	}
	
	@Override
	public final Id subSequence(final int start, final int end) {
		return new Id(this.toString().subSequence(start, end));
	}
	
	private static final long serialVersionUID = -5913031150565988766L;
	
}