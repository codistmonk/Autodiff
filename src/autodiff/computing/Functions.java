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
import java.util.LinkedHashMap;
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
	
	private static final Map<String, List<Object>> definitions = synchronizedMap(new LinkedHashMap<>());
	
	public static final String CASES = "cases";
	
	public static final String IF = "if";
	
	public static final String OTHERWISE = "otherwise";
	
	public static final String FORALL = "forall";
	
	public static final String IN = "in";
	
	public static final String R = "|R";
	
	public static final String ID = "id";
	
	public static final String SQUARED = "^2";
	
	public static final String SQMINUS = "-^2";
	
	public static final String SQRT = "sqrt";
	
	public static final String D = "~d";
	
	public static final String ABS = "abs";
	
	public static final String EXP = "exp";
	
	public static final String LN = "ln";
	
	public static final String SIN = "sin";
	
	public static final String COS = "cos";
	
	public static final String SUM = "sum";
	
	/**
	 * Smoothed half identity.
	 */
	public static final String SHI = "shi";
	
	public static final String SIGMOID = "sigmoid";
	
	public static final String BUMP = "bump";
	
	public static final String RELU = "relu";
	
	public static final String MAX = "max";
	
	public static final String STEP0 = "step0";
	
	public static final String STEP1 = "step1";
	
	public static final String KRONECKER = "kronecker";
	
	public static final double EPSILON = pow(2.0, -14.0);
	
	public static final Collection<String> INFIX_OPERATORS = unmodifiableSet(set("+", "-", "*", "/", SQMINUS, "=", "!=", "<", "<=", ">", ">="));
	
	public static final Collection<String> PREFIX_OPERATORS = unmodifiableSet(set("-", ABS, SHI, SIGMOID, BUMP, RELU, EXP, LN, SIN, COS, SQRT, STEP0, STEP1));
	
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
		
		define("-", x,
				$("-", x));
		defineDiff("-", x,
				-1);
		
		defineDiff(SQUARED, x,
				$(2, "*", x));
		
		define(SQUARED, x, $(x, SQUARED),
				$(x, "*", x));
		defineDiff(SQUARED, x,
				$(2, "*", x));
		
		// TODO asymptotic cases
		define(SHI, x,
				$(LN, $(1, "+", $(EXP, x))));
		// TODO asymptotic cases
		define(SIGMOID, x,
				$(1, "/", $(1, "+", $(EXP, $("-", x)))));
		// TODO asymptotic cases
		define(BUMP, x,
				$($(1, "-", $(SIGMOID, x)), "*", $(SIGMOID, x)));
		
		defineDiff(SHI, x,
				$(SIGMOID, x));
		defineDiff(SIGMOID, x,
				$(BUMP, x));
		
		define(RELU, x,
				$(MAX, 0, x));
		defineDiff(RELU, x,
				$(SIGMOID, x));
		
		define(STEP0, x,
				$(CASES, $(0, IF, $(x, "<", 0)), $(1, OTHERWISE)));
		defineDiff(STEP0, x,
				EPSILON);
		
		define(STEP1, x,
				$(CASES, $(0, IF, $(x, "<=", 0)), $(1, OTHERWISE)));
		defineDiff(STEP1, x,
				EPSILON);
		
		define(KRONECKER, $(x, y),
				$(CASES, $(1, IF, $(x, "=", y)), $(0, OTHERWISE)));
		defineDiff(KRONECKER, 0, $(x, y),
				$(CASES, $(EPSILON, IF, $(x, "<=", y)), $(-EPSILON, OTHERWISE)));
		defineDiff(KRONECKER, 1, $(x, y),
				$(CASES, $(EPSILON, IF, $(y, "<=", x)), $(-EPSILON, OTHERWISE)));
		
		autodefine(SQRT, x);
		defineDiff(SQRT, x,
				$(1, "/", $(2, "*", $(SQRT, x))));
		
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
		defineDiff("+", 0, $(x, y),
				1);
		defineDiff("+", 1, $(x, y),
				1);
		
		autodefineInfix("-", $(x, y));
		defineDiff("-", 0, $(x, y),
				1);
		defineDiff("-", 1, $(x, y),
				-1);
		
		autodefineInfix("*", $(x, y));
		defineDiff("*", 0, $(x, y),
				y);
		defineDiff("*", 1, $(x, y),
				x);
		
		autodefineInfix("/", $(x, y));
		defineDiff("/", 0, $(x, y),
				$(1, "/", y));
		defineDiff("/", 1, $(x, y),
				$($("-", x), "/", $(y, "*", y)));
		
		defineInfix(SQMINUS, $(x, y),
				$($(x, "-", y), SQUARED));
		defineDiff(SQMINUS, 0, $(x, y),
				$(2, "*", $(x, "-", y)));
		defineDiff(SQMINUS, 1, $(x, y),
				$(2, "*", $(y, "-", x)));
	}
	
	public static final Map<String, List<Object>> getDefinitions() {
		return definitions;
	}
	
	public static final void define(final String functionName, final List<Object> variableNames, final List<Object> notation, final Object definition) {
		getDefinitions().put(fName(functionName, variableNames.size()), $(FORALL, variableNames, IN, R, $(notation, "=", definition)));
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
		final List<Object> notation = application($(D, variableIndex, functionName), variableNames);
		
		getDefinitions().put(diffName(fName(functionName, variableNames.size()), variableIndex), $(FORALL, variableNames, IN, R, $(notation, "=", definition)));
	}
	
	public static final List<Object> getDefinition(final String functionName, final int variableCount) {
		return getDefinitions().get(fName(functionName, variableCount));
	}
	
	public static final List<Object> getDiffDefinition(final String functionName, final int variableCount, final int variableIndex) {
		return getDefinitions().get(diffName(fName(functionName, variableCount), variableIndex));
	}
	
	public static final List<Object> getDiffDefinition(final String functionName, final int variableCount) {
		return getDiffDefinition(functionName, variableCount, 0);
	}
	
	public static final String fName(final String functionName, final int variableCount) {
		return functionName + " (" + variableCount + ")";
	}
	
	public static final String diffName(final String functionName, final int variableIndex) {
		return "~d_" + variableIndex + " " + functionName;
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
