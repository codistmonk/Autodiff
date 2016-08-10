package autodiff.reasoning.expressions;

import static java.util.stream.Collectors.toList;

import java.util.List;

/**
 * @author codistmonk (creation 2015-04-17)
 */
public abstract interface ExpressionRewriter extends ExpressionVisitor<Object> {
	
	@Override
	public default Object visit(final Object expression) {
		return expression;
	}
	
	@Override
	public default Object visit(final List<?> expression) {
		return expression.stream().map(this).collect(toList());
	}
	
}