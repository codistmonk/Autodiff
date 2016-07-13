package autodiff.nodes;

import static multij.tools.Tools.cast;

import java.math.BigDecimal;
import java.util.HashMap;
import java.util.Map;

import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class Mapping extends UnaryNode<Mapping> {
	
	private String operation;
	
	@Override
	public final <V> V accept(final NodeVisitor<V> visitor) {
		return visitor.visit(this);
	}
	
	public final String getOperation() {
		return this.operation;
	}
	
	public final Mapping setOperation(final String operation) {
		this.operation = operation;
		
		return this;
	}
	
	@Override
	public final Mapping autoShape() {
		return this.setShape(this.getArgument().getShape());
	}
	
	private static final long serialVersionUID = -2566458738220643925L;
	
	private static final Map<String, Object[]> forwards = new HashMap<>();
	
	private static final Map<String, Object[]> diffs = new HashMap<>();
	
	public static final String FORALL = "\\forall";
	
	public static final String IN = "\\in";
	
	public static final String R = "\\mathbb{R}";
	
	public static final String SQUARED = "^2";
	
	public static final String SQRT = "sqrt";
	
	public static final String TIMES = "\\cdot";
	
	public static final String D = "\\partial";
	
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
		
		define(SQUARED, x, $(x, SQUARED),
				$(x, TIMES, x));
		defineDiff(SQUARED, x,
				$(2, TIMES, x));
		
		define(SHI, x,
				$(LN, $(1, "+", $(EXP, x))));
		defineDiff(SHI, x,
				$(SIGMOID, x));
		
		define(SIGMOID, x,
				$(1, "/", $(1, "+", $(EXP, $("-", x)))));
		defineDiff(SIGMOID, x,
				$($(EXP, x), "/", $($(1, "+", $(EXP, x)), SQUARED)));
		
		define(RELU, x,
				$(MAX, 0, x));
		defineDiff(RELU, x,
				$(SIGMOID, x));
		
		defineDiff(SQRT, x,
				$(1, "/", $(2, TIMES, $(SQRT, x))));
		
		defineDiff(EXP, x,
				$(EXP, x));
		
		defineDiff(LN, x,
				$(1, "/", x));
	}
	
	public static final void define(final String functionName, final String variableName, final Object... definition) {
		forwards.put(functionName, $(FORALL, $(variableName), IN, R, $($(functionName, variableName), "=", definition)));
	}
	
	public static final void define(final String functionName, final String variableName, final Object[] notation, final Object... definition) {
		forwards.put(functionName, $(FORALL, $(variableName), IN, R, $(notation, "=", definition)));
	}
	
	public static final void defineDiff(final String functionName, final String variableName, final Object... definition) {
		diffs.put(functionName, $(FORALL, $(variableName), IN, R, $($($(D, functionName, 0), variableName), "=", definition)));
	}
	
	public static final Object[] $(final Object... objects) {
		final int n = objects.length;
		
		for (int i = 0; i < n; ++i) {
			final Number number = cast(Number.class, objects[i]);
			
			if (number != null && !(number instanceof BigDecimal)) {
				objects[i] = new BigDecimal("" + number);
			}
		}
		
		return objects;
	}
	
}
