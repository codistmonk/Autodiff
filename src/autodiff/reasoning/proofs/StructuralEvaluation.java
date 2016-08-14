package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;

import autodiff.reasoning.expressions.ExpressionRewriter;
import autodiff.reasoning.proofs.Proof.Abstract;

import java.util.List;

/**
 * @author codistmonk (creation 2016-08-14)
 */
public final class StructuralEvaluation extends Abstract {
	
	private final Object formula;
	
	public StructuralEvaluation(final String provedPropositionName,
			final List<Object> message, final Object formula) {
		super(provedPropositionName, message);
		this.formula = formula;
	}
	
	@Override
	public final Object getProvedPropositionFor(final Deduction context) {
		return Evaluator.INSTANCE.apply(this.formula);
	}
	
	private static final long serialVersionUID = -1948317661123881579L;
	
	public static final Object MATCH = $(":=:");
	
	/**
	 * @author codistmonk (creation 2016-08-14)
	 */
	public static final class Evaluator implements ExpressionRewriter {
		
		@Override
		public final Object visit(final List<?> expression) {
			if (3 == expression.size() && MATCH.equals(operator(expression))) {
				return new Substitution.ExpressionEquality().apply(left(expression), right(expression)) ? expression : $(LNOT, expression);
			}
			
			throw new IllegalArgumentException();
		}
		
		private static final long serialVersionUID = 7502840625633463114L;
		
		public static final Evaluator INSTANCE = new Evaluator();
		
	}
	
}
