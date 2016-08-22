package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;

import autodiff.reasoning.expressions.ExpressionRewriter;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author codistmonk (creation 2016-08-22)
 */
public final class BasicStringVerification extends Proof.Abstract {
	
	private final Object proposition;
	
	public BasicStringVerification(final String provedPropositionName, final List<Object> message, final Object proposition) {
		super(provedPropositionName, message);
		this.proposition = proposition;
	}
	
	@Override
	public final Object getProvedPropositionFor(final Deduction context) {
		final Object verification = Verifier.INSTANCE.apply(this.proposition);
		
		if (!(Boolean) verification) {
			return $(LNOT, this.proposition);
		}
		
		return this.proposition;
	}
	
	public static final Object S = $(":S:");
	
	private static final long serialVersionUID = -7412657081489798543L;
	
	/**
	 * @author codistmonk (creation 2016-01-30)
	 */
	public static final class Verifier implements ExpressionRewriter {
		
		@Override
		public final Object visit(final List<?> expression) {
			@SuppressWarnings("unchecked")
			final List<Object> list = (List<Object>) ExpressionRewriter.super.visit(expression);
			
			if (2 == list.size()) {
				return UnaryOperator.decode(list.get(0)).compute(
						(String) list.get(1));
			}
			
			if (3 == list.size()) {
				return BinaryOperator.decode(list.get(1)).compute(
						list.get(0), list.get(2));
			}
			
			throw new IllegalArgumentException("Failed to evaluate: " + expression);
		}
		
		private static final long serialVersionUID = -9089588808047854990L;
		
		public static final Verifier INSTANCE = new Verifier();
		
	}
	
	/**
	 * @author codistmonk (creation 2016-09-30)
	 */
	public static enum UnaryOperator {
		
		LENGTH {
			
			@Override
			public final BigDecimal compute(final String operand) {
				return new BigDecimal(operand.length());
			}
			
		};
		
		public abstract Object compute(String operand);
		
		private static final Map<Object, UnaryOperator> operators = new HashMap<>();
		
		static {
			operators.put($("length"), LENGTH);
		}
		
		public static final UnaryOperator decode(final Object operator) {
			if (operator instanceof UnaryOperator) {
				return (UnaryOperator) operator;
			}
			
			final UnaryOperator result = operators.get(operator);
			
			if (result == null) {
				throw new IllegalArgumentException("Invalid operator: " + operator);
			}
			
			return result;
		}
		
	}
	
	/**
	 * @author codistmonk (creation 2016-09-30)
	 */
	public static enum BinaryOperator {
		
		ADD {
			
			@Override
			public final String compute(final Object left, final Object right) {
				checkArgument(right instanceof String || right instanceof Number,
						"Incorrect type: " + (right != null ? right.getClass().toString() : "?"));
				
				return (String) left + right;
			}
			
		}, EQUAL {
			
			@Override
			public final Boolean compute(final Object left, final Object right) {
				return left instanceof String && left.equals(right);
			}
			
		}, MEMBERSHIP {
			
			@Override
			public final Boolean compute(final Object left, final Object right) {
				return left instanceof String && S.equals(right);
			}
			
		};
		
		public abstract Object compute(Object left, Object right);
		
		private static final Map<Object, BinaryOperator> operators = new HashMap<>();
		
		static {
			operators.put($("+"), ADD);
			operators.put($("="), EQUAL);
			operators.put($("∈"), MEMBERSHIP);
		}
		
		public static final BinaryOperator decode(final Object operator) {
			if (operator instanceof BinaryOperator) {
				return (BinaryOperator) operator;
			}
			
			final BinaryOperator result = operators.get(operator);
			
			if (result == null) {
				throw new IllegalArgumentException("Invalid operator: " + operator);
			}
			
			return result;
		}
		
	}
	
}
