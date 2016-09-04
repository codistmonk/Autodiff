package autodiff.reasoning.proofs;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.rules.PatternPredicate.rule;
import static java.util.stream.Collectors.toList;
import static multij.tools.Tools.cast;
import static multij.tools.Tools.ignore;

import autodiff.reasoning.expressions.ExpressionRewriter;
import autodiff.rules.Rules;
import autodiff.rules.Variable;

import java.math.BigDecimal;
import java.util.Collection;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-08-22)
 */
public final class ElementaryVerification extends Proof.Abstract {
	
	private final Object proposition;
	
	public ElementaryVerification(final String provedPropositionName, final List<Object> message, final Object proposition) {
		super(provedPropositionName, message);
		this.proposition = proposition;
	}
	
	@Override
	public final Object getProvedPropositionFor(final Deduction context) {
		final Object verification = Evaluator.INSTANCE.apply(this.proposition);
		
		if (!(Boolean) verification) {
			return $(LNOT, this.proposition);
		}
		
		return this.proposition;
	}
	
	private static final long serialVersionUID = 8999913520315300571L;
	
	public static final Object N = $("ℕ");
	
	public static final Object Z = $("ℤ");
	
	public static final Object Q = $("ℚ");
	
	public static final Object R = $("ℝ");
	
	public static final Object STRING = $("String");
	
	public static final Object norm(final Object expression) {
		return $("|", expression, "|");
	}
	
	/**
	 * @author codistmonk (creation 2016-08-22)
	 */
	public static final class Evaluator implements ExpressionRewriter {
		
		private final Rules<Object, Object> rules = new Rules<>();
		
		{
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "+", vy), (e, m) -> {
					final Object x = vx.get();
					final Object y = vy.get();
					final String sx = cast(String.class, x);
					final String sy = cast(String.class, y);
					
					if (sx != null && sy != null) {
						return sx + sy;
					}
					
					final BigDecimal nx = cast(BigDecimal.class, $n(x));
					final BigDecimal ny = cast(BigDecimal.class, $n(y));
					
					if (nx != null && ny != null) {
						return nx.add(ny);
					}
					
					if (sx != null && ny != null) {
						return sx + ny;
					}
					
					if (nx != null && sy != null) {
						return nx + sy;
					}
					
					return null;
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "-", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.subtract(ny);
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "*", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.multiply(ny);
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "/", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.divide(ny);
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "^", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.pow(ny.intValueExact());
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "%", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.remainder(ny);
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "<<", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return new BigDecimal(nx.toBigIntegerExact().shiftLeft(ny.intValueExact()));
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, ">>", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return new BigDecimal(nx.toBigIntegerExact().shiftRight(ny.intValueExact()));
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "|", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return new BigDecimal(nx.toBigIntegerExact().or(ny.toBigIntegerExact()));
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "&", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return new BigDecimal(nx.toBigIntegerExact().and(ny.toBigIntegerExact()));
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "¨", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return new BigDecimal(nx.toBigIntegerExact().xor(ny.toBigIntegerExact()));
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "<", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.compareTo(ny) < 0;
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "<=", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.compareTo(ny) <= 0;
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, LE, vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.compareTo(ny) <= 0;
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, ">", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.compareTo(ny) > 0;
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, ">=", vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.compareTo(ny) >= 0;
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, GE, vy), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					final BigDecimal ny = $n(vy.get());
					
					return nx.compareTo(ny) >= 0;
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				
				this.rules.add(rule($("-", vx), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					
					return nx.negate();
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				
				this.rules.add(rule($("floor", vx), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					
					return nx.setScale(0, BigDecimal.ROUND_FLOOR);
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				
				this.rules.add(rule($("ceiling", vx), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					
					return nx.setScale(0, BigDecimal.ROUND_CEILING);
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				
				this.rules.add(rule($("~", vx), (e, m) -> {
					final BigDecimal nx = $n(vx.get());
					
					return new BigDecimal(nx.toBigIntegerExact().not());
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				
				this.rules.add(rule(norm(vx), (e, m) -> {
					final String sx = cast(String.class, vx.get());
					
					if (sx != null) {
						return BigDecimal.valueOf(sx.length());
					}
					
					final BigDecimal nx = $n(vx.get());
					
					return nx.abs();
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				
				this.rules.add(rule($(LNOT, vx), (e, m) -> {
					return !(Boolean) vx.get();
				}));
			}
			
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				final Collection<Object> knownSets = Tools.set(N, Z, Q, R, STRING);
				
				this.rules.add(rule($(vx, IN, vy), (e, m) -> {
					final Object x = vx.get();
					final Object y = vy.get();
					
					if (!knownSets.contains(y)) {
						return null;
					}
						
					final String sx = cast(String.class, x);
					final BigDecimal nx = cast(BigDecimal.class, $n(x));
					
					if (sx == null && nx == null) {
						return null;
					}
					
					if (STRING.equals(y)) {
						return sx != null;
					}
					
					if (nx == null) {
						return false;
					}
					
					if (R.equals(y) || Q.equals(y)) {
						return true;
					}
					
					try {
						nx.toBigIntegerExact();
					} catch (final ArithmeticException exception) {
						ignore(exception);
						
						return false;
					}
					
					if (Z.equals(y)) {
						return true;
					}
					
					if (0 <= nx.compareTo(BigDecimal.ZERO) && N.equals(y)) {
						return true;
					}
					
					return false;
				}));
			}
			{
				final Variable vx = new Variable("x");
				final Variable vy = new Variable("y");
				
				this.rules.add(rule($(vx, "=", vy), (e, m) -> {
					final Object x = vx.get();
					final Object y = vy.get();
					
					if (x.equals(y)) {
						return true;
					}
					
					final String sx = cast(String.class, x);
					final String sy = cast(String.class, y);
					final BigDecimal nx = cast(BigDecimal.class, $n(x));
					final BigDecimal ny = cast(BigDecimal.class, $n(y));
					
					if (sx != null && (sy != null || ny != null) || nx != null && sy != null) {
						return false;
					}
					
					if (nx != null && ny != null) {
						return nx.equals(ny);
					}
					
					return null;
				}));
			}
			
			{
				this.rules.add(rule(new Variable("*"), (e, m) -> e));
			}
		}
		
		@Override
		public final Object visit(final List<?> expression) {
			final List<Object> arguments = expression.stream().map(this).collect(toList());
			
			return this.rules.apply(arguments);
		}
		
		private static final long serialVersionUID = -9089588808047854990L;
		
		public static final Evaluator INSTANCE = new Evaluator();
		
	}
	
	/**
	 * @author codistmonk (creation 2016-09-30)
	 */
	public static enum UnaryOperator {
		
		NEGATION {
			
			@Override
			public final BigDecimal compute(final BigDecimal operand) {
				return operand.negate();
			}
			
		}, ABSOLUTE_VALUE {
			
			@Override
			public final BigDecimal compute(final BigDecimal operand) {
				return operand.abs();
			}
			
		}, FLOOR {
			
			@Override
			public final BigDecimal compute(final BigDecimal operand) {
				return operand.setScale(0, BigDecimal.ROUND_FLOOR);
			}
			
		}, CEILING {
			
			@Override
			public final BigDecimal compute(final BigDecimal operand) {
				return operand.setScale(0, BigDecimal.ROUND_CEILING);
			}
			
		}, BITWISE_NEGATION {
			
			@Override
			public final BigDecimal compute(final BigDecimal operand) {
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
