package autodiff.nodes;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.BasicNumericVerification.*;
import static autodiff.reasoning.proofs.Stack.*;
import static multij.tools.Tools.*;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import autodiff.reasoning.deductions.Standard;
import autodiff.reasoning.proofs.Deduction;

/**
 * @author codistmonk (creation 2016-08-09)
 */
public final class ComputationNode extends AbstractNode<ComputationNode> {
	
	private final Map<String, Object> bindings;
	
	private List<Object> definition;
	
	private final List<BindListener> bindListeners;
	
	public ComputationNode() {
		super(new ArrayList<>());
		this.bindings = new LinkedHashMap<>();
		this.definition = new ArrayList<>();
		this.bindListeners = new ArrayList<>();
	}
	
	public final List<BindListener> getBindListeners() {
		return this.bindListeners;
	}
	
	public final Map<String, Object> getBindings() {
		return this.bindings;
	}
	
	public final ComputationNode bind(final String key, final Object value) {
		this.getBindListeners().forEach(l -> l.beforeBind(key, value));
		this.getBindings().put(key, value);
		this.getBindListeners().forEach(l -> l.afterBind(key, value));
		
		return this;
	}
	
	public final List<Object> getDefinition() {
		return this.definition;
	}
	
	public final ComputationNode setDefinition(final List<Object> definition) {
		this.definition = definition;
		
		return this;
	}
	
	@Override
	public final ComputationNode autoShape() {
		// TODO Auto-generated method stub
		return super.autoShape();
	}
	
	private static final long serialVersionUID = 2834011599617369367L;
	
	public static final Object IN = $("∈");
	
	public static final Object CROSS = $("×");

	public static final Object PI = $("Π");
	
	public static final Object POS = $(N, "_", $(">", 0));
	
	public static final Deduction AUTODIFF = Standard.build("autodiff", new Runnable() {
		
		@Override
		public final void run() {
			Standard.setup();
			// TODO Auto-generated method stub
			
			{
				final Object _x = $new("x");
				final Object _X = $new("X");
				final Object _P = $new("P");
				
				suppose("definition_of_forall_in", $forall(_x, _X, _P,
						$($(FORALL, _x, IN, _X, _P), "=", $forall(_x, $rule($(_x, IN, _X), _P)))));
			}
			
			{
				final Object _n = $new("n");
				final Object _s = $new("s");
				
				suppose("definition_of_M_s",
						$(FORALL, _n, IN, POS,
								$(FORALL, _s, IN, $(POS, "^", _n,
										$($("M", "_", _s), "=", $($(R, "^", $(PI, _s)), CROSS, c(_s)))))));
			}
			
			{
				final Object _n = $new("n");
				final Object _s = $new("s");
				final Object _X = $new("X");
				final Object _i = $new("i");
				
				suppose("type_of_flat",
						$(FORALL, _n, IN, POS,
								$(FORALL, _s, IN, $(POS, "^", _n,
										$forall(_X, $($("flat", " ", $(p(1), "_", $(_i, IN, _s))), IN, $(R, "^", $(PI, _s))))))));
			}
			
			{
				final Object _X = $new("X");
				
				suppose("definition_of_singleton",
						$forall(_X,
								$(_X, IN, c(_X))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				final Object _x = $new("x");
				final Object _y = $new("y");
				
				suppose("type_of_pair",
						$forall(_X, _Y,
								$(FORALL, _x, IN, _X,
										$(FORALL, _y, IN, _Y,
												$(p(_x, ",", _y), IN, $(_X, CROSS, _Y))))));
			}
			
			abort();
		}
		
	}, 1);
	
	public static final ComputationNode ones() {
		final ComputationNode result = new ComputationNode();
		
		final Object n = $new("n");
		final Object s = $new("s");
		final Object i = $new("i");
		
		result.setDefinition(
				$(FORALL, n, IN, POS,
						$(FORALL, s, IN, $(POS, "^", n),
								$($("ones", " ", s), "=", p($("flat", " ", $(p(1), "_", $(i, IN, s))), ",", s)))));
		
		result.bind("s", null);
		
		result.getBindListeners().add(new BindListener() {
			
			@Override
			public final void beforeBind(final String key, final Object value) {
				if ("s".equals(key)) {
					final int[] shape = (int[]) value;
					
					NodesTools.check(0 < shape.length, () -> "Invalid shape: []");
					
					result.bind("n", shape.length);
				}
			}
			
			private static final long serialVersionUID = -64734290035563118L;
			
		});
		
		debugPrint(deepJoin(" ", result.getDefinition()));
		debugPrint(result.getBindings().keySet());
		
		return result;
	}
	
	public static final List<Object> p(final Object... objects) {
		return $("(", $(objects), ")");
	}
	
	public static final List<Object> c(final Object... objects) {
		return $("{", $(objects), "}");
	}
	
	public static final String deepJoin(final String separator, final Iterable<?> objects) {
		final StringBuilder resultBuilder = new StringBuilder();
		boolean first = true;
		
		for (final Object object : objects) {
			final Iterable<?> subobjects = cast(Iterable.class, object);
			
			if (first) {
				first = false;
			} else {
				resultBuilder.append(separator);
			}
			
			resultBuilder.append(subobjects == null ? object : deepJoin(separator, subobjects));
		}
		
		return resultBuilder.toString();
	}
	
	/**
	 * @author codistmonk (creation 2016-08-10)
	 */
	public static abstract interface BindListener extends Serializable {
		
		public default void beforeBind(final String key, final Object value) {
			// NOP
		}
		
		public default void afterBind(final String key, final Object value) {
			// NOP
		}
		
	}
	
}
