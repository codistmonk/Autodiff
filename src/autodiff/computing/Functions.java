package autodiff.computing;

import static java.lang.Math.pow;
import static java.util.Collections.synchronizedMap;
import static java.util.Collections.unmodifiableSet;
import static multij.tools.Tools.cast;
import static multij.tools.Tools.set;

import java.math.BigDecimal;
import java.util.Arrays;
import java.util.Collection;
import java.util.Collections;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

import multij.tools.IllegalInstantiationException;

/**
 * @author codistmonk (creation 2016-07-13)
 */
public final class Functions {
	
	private Functions() {
		throw new IllegalInstantiationException();
	}
	
	private static final Map<String, List<Object>> forwards = synchronizedMap(new HashMap<>());
	
	private static final Map<String, List<Object>> diffs = synchronizedMap(new HashMap<>());
	
	public static final String CASES = "cases";
	
	public static final String IF = "if";
	
	public static final String OTHERWISE = "otherwise";
	
	public static final String FORALL = "forall";
	
	public static final String IN = "in";
	
	public static final String R = "|R";
	
	public static final String ID = "id";
	
	public static final String SQUARED = "^2";
	
	public static final String SQRT = "sqrt";
	
	public static final String TIMES = ".*";
	
	public static final String D = "~d";
	
	public static final String ABS = "abs";
	
	public static final String NEG = "neg";
	
	public static final String EXP = "exp";
	
	public static final String LN = "ln";
	
	public static final String SIN = "sin";
	
	public static final String COS = "cos";
	
	/**
	 * Smoothed half identity.
	 */
	public static final String SHI = "shi";
	
	public static final String SIGMOID = "sigmoid";
	
	public static final String BUMP = "bump";
	
	public static final String RELU = "relu";
	
	public static final String MAX = "max";
	
	public static final String STEP = "step";
	
	public static final double EPSILON = pow(2.0, -14.0);
	
	public static final Collection<String> INFIX_OPERATORS = unmodifiableSet(set("+", "-", TIMES, "/", "=", "!=", "<", "<=", ">", ">="));
	
	public static final Collection<String> PREFIX_OPERATORS = unmodifiableSet(set("-", ABS, SHI, SIGMOID, BUMP, RELU, EXP, LN, SIN, COS, SQRT, STEP));
	
	public static final Collection<String> POSTFIX_OPERATORS = unmodifiableSet(set(SQUARED));
	
	static {
		final String x = "x";
		final String y = "y";
		
		define(ID, x,
				x);
		defineDiff(ID, x,
				1);
		
		autodefine(ABS, x);
		defineDiff(ABS, x,
				1);
		
		define(NEG, x,
				$("-", x));
		defineDiff(NEG, x,
				-1);
		
		defineDiff(SQUARED, x,
				$(2, TIMES, x));
		
		define(SQUARED, x, $(x, SQUARED),
				$(x, TIMES, x));
		defineDiff(SQUARED, x,
				$(2, TIMES, x));
		
		// TODO asymptotic cases
		define(SHI, x,
				$(LN, $(1, "+", $(EXP, x))));
		// TODO asymptotic cases
		define(SIGMOID, x,
				$(1, "/", $(1, "+", $(EXP, $("-", x)))));
		// TODO asymptotic cases
		define(BUMP, x,
				$($(1, "-", $(SIGMOID, x)), TIMES, $(SIGMOID, x)));
		
		defineDiff(SHI, x,
				$(SIGMOID, x));
		defineDiff(SIGMOID, x,
				$(BUMP, x));
		
		define(RELU, x,
				$(MAX, 0, x));
		defineDiff(RELU, x,
				$(SIGMOID, x));
		
		define(STEP, x,
				$(CASES, $(0, IF, $(x, "<", 0)), $(1, OTHERWISE)));
		defineDiff(STEP, x,
				EPSILON);
		
		autodefine(SQRT, x);
		defineDiff(SQRT, x,
				$(1, "/", $(2, TIMES, $(SQRT, x))));
		
		autodefine(EXP, x);
		defineDiff(EXP, x,
				$(EXP, x));
		
		autodefine(LN, x);
		defineDiff(LN, x,
				$(1, "/", x));
		
		autodefine(SIN, x);
		defineDiff(SIN, x,
				$(COS, x));
		
		autodefine(COS, x);
		defineDiff(COS, x,
				$("-", $(SIN, x)));
		
		autodefineInfix("+", $(x, y));
		defineDiff("+", 0, $(x, y), 1);
		defineDiff("+", 1, $(x, y), 1);
		
		autodefineInfix("-", $(x, y));
		defineDiff("-", 0, $(x, y), 1);
		defineDiff("-", 1, $(x, y), -1);
		
		autodefineInfix(TIMES, $(x, y));
		defineDiff(TIMES, 0, $(x, y), y);
		defineDiff(TIMES, 1, $(x, y), x);
		
		autodefineInfix("/", $(x, y));
		defineDiff("/", 0, $(x, y), $(1, "/", y));
		defineDiff("/", 1, $(x, y), $($("-", x), "/", $(y, TIMES, y)));
	}
	
	public static final Map<String, List<Object>> getForwards() {
		return forwards;
	}
	
	public static final Map<String, List<Object>> getDiffs() {
		return diffs;
	}
	
	public static final void define(final String functionName, final List<Object> variableNames, final List<Object> notation, final Object definition) {
		getForwards().put(functionName, $(FORALL, variableNames, IN, R, $(notation, "=", definition)));
	}
	
	public static final void defineInfix(final String functionName, final List<Object> variableNames, final Object definition) {
		define(functionName, variableNames, $(variableNames.get(0), functionName, variableNames.get(1)), definition);
	}
	
	public static final void autodefineInfix(final String functionName, final List<Object> variableNames) {
		final List<Object> notation = $(variableNames.get(0), functionName, variableNames.get(1));
		
		define(functionName, variableNames, notation, notation);
	}
	
	public static final void define(final String functionName, final List<Object> variableNames, final Object definition) {
		final List<Object> notation = application(functionName, variableNames);
		
		define(functionName, variableNames, notation, definition);
	}
	
	public static final List<Object> application(final Object function, final List<Object> variableNames) {
		final List<Object> result = $(new Object[1 + variableNames.size()]);
		
		result.set(0, function);
		
		Collections.copy(result.subList(1, result.size()), variableNames);
		
		return result;
	}
	
	public static final void define(final String functionName, final String variableName, final Object definition) {
		define(functionName, $(variableName), definition);
	}
	
	public static final void define(final String functionName, final String variableName, final List<Object> notation, final Object definition) {
		define(functionName, $(variableName), notation, definition);
	}
	
	public static final void autodefine(final String functionName, final String variableName) {
		final List<Object> notation = $(functionName, variableName);
		
		define(functionName, $(variableName), notation, notation);
	}
	
	public static final void defineDiff(final String functionName, final String variableName, final Object definition) {
		defineDiff(functionName, 0, $(variableName), definition);
	}
	
	public static final void defineDiff(final String functionName, final int variableIndex, final List<Object> variableNames, final Object definition) {
		final List<Object> notation = application($(D, functionName, variableIndex), variableNames);
		
		getDiffs().put(functionName + "." + variableIndex, $(FORALL, variableNames, IN, R, $(notation, "=", definition)));
	}
	
	public static final List<Object> getForward(final String functionName) {
		return getForwards().get(functionName);
	}
	
	public static final List<Object> getDiff(final String functionName) {
		return getDiffs().get(functionName);
	}
	
	public static final Object n(final Object object) {
		final Number number = cast(Number.class, object);
		
		if (number != null && !(number instanceof BigDecimal)) {
			return new BigDecimal("" + number);
		}
		
		return object;
	}
	
	public static final List<Object> $(final Object... objects) {
		final int n = objects.length;
		
		for (int i = 0; i < n; ++i) {
			objects[i] = n(objects[i]);
		}
		
		return Arrays.asList(objects);
	}
	
}
