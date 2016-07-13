package autodiff.nodes;

import static java.lang.Math.pow;
import static multij.tools.Tools.cast;

import java.math.BigDecimal;
import java.util.Arrays;
import java.util.HashMap;
import java.util.List;
import java.util.Map;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Mapping extends UnaryNode<Mapping> {
	
	private String functionName;
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	public final String getFunctionName() {
		return this.functionName;
	}
	
	public final Mapping setFunctioName(final String functionName) {
		this.functionName = functionName;
		
		return this;
	}
	
	@Override
	public final Mapping autoShape() {
		return this.setShape(this.getArgument().getShape());
	}
	
	private static final long serialVersionUID = -2566458738220643925L;
	
	private static final Map<String, List<Object>> forwards = new HashMap<>();
	
	private static final Map<String, List<Object>> diffs = new HashMap<>();
	
	public static final String FORALL = "\\forall";
	
	public static final String IN = "\\in";
	
	public static final String R = "\\mathbb{R}";
	
	public static final String ID = "id";
	
	public static final String SQUARED = "^2";
	
	public static final String SQRT = "sqrt";
	
	public static final String TIMES = "\\cdot";
	
	public static final String D = "\\partial";
	
	public static final String ABS = "\\abs";
	
	public static final String NEG = "\\neg";
	
	public static final String EXP = "\\exp";
	
	public static final String LN = "\\ln";
	
	/**
	 * Smoothed half identity.
	 */
	public static final String SHI = "\\shi";
	
	public static final String SIGMOID = "\\sigmoid";
	
	public static final String BUMP = "\\bump";
	
	public static final String RELU = "\\relu";
	
	public static final String MAX = "\\max";
	
	public static final String STEP = "\\step";
	
	static {
		final String x = "x";
		final double epsilon = pow(2.0, -14.0);
		
		define(ID, x,
				x);
		defineDiff(ID, x,
				1);
		
		define(ABS, x,
				$(ABS, x));
		defineDiff(ABS, x,
				1);
		
		define(NEG, x,
				$(NEG, x));
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
				$("cases", $(0, "if", $(x, "<", 0)), $(1, "otherwise")));
		defineDiff(STEP, x,
				epsilon);
		
		define(SQRT, x,
				$(SQRT, x));
		defineDiff(SQRT, x,
				$(1, "/", $(2, TIMES, $(SQRT, x))));
		
		define(EXP, x,
				$(EXP, x));
		defineDiff(EXP, x,
				$(EXP, x));
		
		define(LN, x,
				$(LN, x));
		defineDiff(LN, x,
				$(1, "/", x));
	}
	
	public static final void define(final String functionName, final String variableName, final Object definition) {
		forwards.put(functionName, $(FORALL, $(variableName), IN, R, $($(functionName, variableName), "=", definition)));
	}
	
	public static final void define(final String functionName, final String variableName, final List<Object> notation, final Object definition) {
		forwards.put(functionName, $(FORALL, $(variableName), IN, R, $(notation, "=", definition)));
	}
	
	public static final void defineDiff(final String functionName, final String variableName, final Object definition) {
		diffs.put(functionName, $(FORALL, $(variableName), IN, R, $($($(D, functionName, 0), variableName), "=", definition)));
	}
	
	public static final List<Object> getForward(final String functionName) {
		return forwards.get(functionName);
	}
	
	public static final List<Object> getDiff(final String functionName) {
		return diffs.get(functionName);
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
