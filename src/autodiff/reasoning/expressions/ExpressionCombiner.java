package autodiff.reasoning.expressions;

import java.util.ArrayList;
import java.util.List;

/**
 * @author codistmonk (creation 2015-04-19)
 */
public abstract interface ExpressionCombiner extends ExpressionZipper<Object> {
	
	@Override
	public default Object visit(final List<?> expression1, final List<?> expression2) {
		final int n = expression1.size();
		
		if (n != expression2.size()) {
			return null;
		}
		
		final List<Object> result = new ArrayList<>(n);
		
		for (int i = 0; i < n; ++i) {
			final Object element = this.apply(expression1.get(i), expression2.get(i));
			
			if (element == null) {
				return null;
			}
			
			result.add(element);
		}
		
		return result;
	}
	
}