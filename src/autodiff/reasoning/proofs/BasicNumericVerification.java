package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;
import static multij.tools.Tools.ignore;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import autodiff.reasoning.expressions.ExpressionRewriter;

/**
 * @author codistmonk (creation 2016-01-30)
 */
public final class BasicNumericVerification extends Proof.Abstract {
	
	private final Object proposition;
	
	public BasicNumericVerification(final String provedPropositionName, final List<Object> message, final Object proposition) {
		super(provedPropositionName, message);
		this.proposition = proposition;
	}
	
	@Override
	public final Object getProvedPropositionFor(final Deduction context) {
		final Object verification = Verifier.INSTANCE.apply(this.proposition);
		
		if (!(Boolean) verification) {
			throw new IllegalArgumentException("Invalid: " + this.proposition + " verification: " + verification);
		}
		
		return this.getProvedProposition();
	}
	
	public final synchronized Object getProvedProposition() {
		return this.proposition;
	}
	
	private static final long serialVersionUID = 8999913520315300571L;
	
	public static final Object N = $("ℕ");
	
	public static final Object Z = $("ℤ");
	
	public static final Object Q = $("ℚ");
	
	public static final Object R = $("ℝ");
	
	@SuppressWarnings("unchecked")
	public static final <T> T numberOrObject(final Object object) {
		if (object instanceof BigDecimal) {
			return (T) object;
		}
		
		if (object instanceof Number) {
			return (T) new BigDecimal(object.toString());
		}
		
		return (T) object;
	}
	
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
						numberOrObject(list.get(1)));
			}
			
			if (3 == list.size()) {
				return BinaryOperator.decode(list.get(1)).compute(
						numberOrObject(list.get(0)), numberOrObject(list.get(2)));
			}
			
			throw new IllegalArgumentException();
		}
		
		private static final long serialVersionUID = -9089588808047854990L;
		
		public static final Verifier INSTANCE = new Verifier();
		
	}
	
	/**
	 * @author codistmonk (creation 2016-09-30)
	 */
	public static enum UnaryOperator {
		
		NEGATION {
			
			@Override
			public BigDecimal compute(final BigDecimal operand) {
				return operand.negate();
			}
			
		}, ABSOLUTE_VALUE {
			
			@Override
			public BigDecimal compute(final BigDecimal operand) {
				return operand.abs();
			}
			
		}, FLOOR {
			
			@Override
			public BigDecimal compute(final BigDecimal operand) {
				return operand.setScale(0, BigDecimal.ROUND_FLOOR);
			}
			
		}, CEILING {
			
			@Override
			public BigDecimal compute(final BigDecimal operand) {
				return operand.setScale(0, BigDecimal.ROUND_CEILING);
			}
			
		}, BITWISE_NEGATION {
				
				@Override
				public BigDecimal compute(final BigDecimal operand) {
					return new BigDecimal(operand.toBigIntegerExact().not());
				}
				
		};
		
		public abstract Object compute(BigDecimal operand);
		
		private static final Map<Object, UnaryOperator> operators = new HashMap<>();
		
		static {
			operators.put($("-"), NEGATION);
			operators.put($("abs"), ABSOLUTE_VALUE);
			operators.put($("floor"), FLOOR);
			operators.put($("ceiling"), CEILING);
			operators.put($("~"), BITWISE_NEGATION);
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
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return left.add((BigDecimal) right);
			}
			
		}, SUBTRACT {
			
			@Override
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return left.subtract((BigDecimal) right);
			}
			
		}, MULTIPLY {
			
			@Override
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return left.multiply((BigDecimal) right);
			}
			
		}, DIVIDE {
			
			@Override
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return left.divide((BigDecimal) right);
			}
			
		}, REMAINDER {
			
			@Override
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return left.remainder((BigDecimal) right);
			}
			
		}, POWER {
			
			@Override
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return left.pow(((BigDecimal) right).intValueExact());
			}
			
		}, BITWISE_SHIFT_LEFT {
			
			@Override
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return new BigDecimal(left.toBigIntegerExact().shiftLeft(((BigDecimal) right).intValueExact()));
			}
			
		}, BITWISE_SHIFT_RIGHT {
			
			@Override
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return new BigDecimal(left.toBigIntegerExact().shiftRight(((BigDecimal) right).intValueExact()));
			}
			
		}, BITWISE_AND {
			
			@Override
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return new BigDecimal(left.toBigIntegerExact().and(((BigDecimal) right).toBigIntegerExact()));
			}
			
		}, BITWISE_OR {
			
			@Override
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return new BigDecimal(left.toBigIntegerExact().or(((BigDecimal) right).toBigIntegerExact()));
			}
			
		}, BITWISE_XOR {
			
			@Override
			public final BigDecimal compute(final BigDecimal left, final Object right) {
				return new BigDecimal(left.toBigIntegerExact().xor(((BigDecimal) right).toBigIntegerExact()));
			}
			
		}, EQUAL {
			
			@Override
			public final Boolean compute(final BigDecimal left, final Object right) {
				return left.equals(right);
			}
			
		}, LESS {
			
			@Override
			public final Boolean compute(final BigDecimal left, final Object right) {
				return left.compareTo((BigDecimal) right) < 0;
			}
			
		}, LESS_OR_EQUAL {
			
			@Override
			public final Boolean compute(final BigDecimal left, final Object right) {
				return left.compareTo((BigDecimal) right) <= 0;
			}
			
		}, GREATER {
			
			@Override
			public final Boolean compute(final BigDecimal left, final Object right) {
				return left.compareTo((BigDecimal) right) > 0;
			}
			
		}, GREATER_OR_EQUAL {
			
			@Override
			public final Boolean compute(final BigDecimal left, final Object right) {
				return left.compareTo((BigDecimal) right) >= 0;
			}
			
		}, MEMBERSHIP {
			
			@Override
			public final Boolean compute(final BigDecimal left, final Object right) {
				if (R.equals(right) || Q.equals(right)) {
					return true;
				}
				
				try {
					left.toBigIntegerExact();
				} catch (final ArithmeticException exception) {
					ignore(exception);
					
					return false;
				}
				
				if (Z.equals(right)) {
					return true;
				}
				
				if (0 <= left.compareTo(BigDecimal.ZERO) && N.equals(right)) {
					return true;
				}
				
				return false;
			}
			
		};
		
		public abstract Object compute(BigDecimal left, Object right);
		
		private static final Map<Object, BinaryOperator> operators = new HashMap<>();
		
		static {
			operators.put($("+"), ADD);
			operators.put($("-"), SUBTRACT);
			operators.put($(" "), MULTIPLY);
			operators.put($("*"), MULTIPLY);
			operators.put($("/"), DIVIDE);
			operators.put($("%"), REMAINDER);
			operators.put($("^"), POWER);
			operators.put($("<<"), BITWISE_SHIFT_LEFT);
			operators.put($(">>"), BITWISE_SHIFT_RIGHT);
			operators.put($("&"), BITWISE_AND);
			operators.put($("|"), BITWISE_OR);
			operators.put($("(^)"), BITWISE_XOR);
			operators.put($("="), EQUAL);
			operators.put($("<"), LESS);
			operators.put($("<="), LESS_OR_EQUAL);
			operators.put($("≤"), LESS_OR_EQUAL);
			operators.put($(">"), GREATER);
			operators.put($(">="), GREATER_OR_EQUAL);
			operators.put($("≥"), GREATER_OR_EQUAL);
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
