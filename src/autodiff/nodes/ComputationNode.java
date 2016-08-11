package autodiff.nodes;

import static autodiff.reasoning.deductions.Standard.rewrite;
import static autodiff.reasoning.deductions.Standard.rewriteRight;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.BasicNumericVerification.*;
import static autodiff.reasoning.proofs.Stack.*;
import static multij.tools.Tools.*;
import autodiff.reasoning.deductions.Standard;
import autodiff.reasoning.expressions.Expressions;
import autodiff.reasoning.proofs.Deduction;

import java.io.Serializable;
import java.util.ArrayList;
import java.util.Arrays;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-08-09)
 */
public final class ComputationNode extends AbstractNode<ComputationNode> {
	
	private final Map<String, Object> bindings;
	
	private List<Object> definition;
	
	private final List<BindListener> bindListeners;
	
	private String typeName;
	
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
	
	public final Object get(final String key) {
		return this.getBindings().get(key);
	}
	
	public final ComputationNode set(final String key, final Object value) {
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
	
	public final String getTypeName() {
		return this.typeName;
	}
	
	public final ComputationNode setTypeName(final String typeName) {
		this.typeName = typeName;
		
		return this;
	}
	
	@Override
	public final String getName() {
		return "[" + this.getId() + "]" + this.getTypeName();
	}
	
	@Override
	public final ComputationNode autoShape() {
		Standard.build(new Deduction(AUTODIFF, this.getName() + "_type"), new Runnable() {
			
			@Override
			public final void run() {
				suppose(getDefinition());
				
				Tools.debugPrint(getDefinition().get(0));
				Tools.debugPrint(getDefinition().get(1));
				Tools.debugPrint(getDefinition().get(2));
				Tools.debugPrint(getDefinition().get(3));
				Tools.debugPrint(getDefinition().get(4));
				
				canonicalizeForallIn(name(-1));
				
				{
					subdeduction();
					
					bind(name(-1), get("n"));
					
					deducePositivity(get("n"));
					
					apply(name(-2), name(-1));
					
					conclude();
				}
				
				canonicalizeForallIn(name(-1));
				
				final Object s = p(Expressions.join(",", Arrays.asList(Arrays.stream((int[]) get("s")).mapToObj(Integer::new).toArray())));
				
				bind(name(-1), s);
				
				{
					subdeduction();
					
					deducePositivity(2);
					
					bind("definition_of_parentheses", 2);
					rewriteRight(name(-2), name(-1));
					
					canonicalizeForallIn("cartesian_1");
					bind(name(-1), POS);
					
					// TODO
					
					conclude();
				}
				
				abort();
			}
		}, 1);
		
		return super.autoShape();
	}
	
	private static final long serialVersionUID = 2834011599617369367L;
	
	public static final Object U = $("℧");
	
	public static final Object IN = $("∈");
	
	public static final Object SUBSET = $("⊂");
	
	public static final Object P = $("ℙ");
	
	public static final Object CROSS = $("×");

	public static final Object PI = $("Π");
	
	public static final Object POS = $(N, "_", $(">", 0));
	
	public static final Deduction AUTODIFF = Standard.build("autodiff", new Runnable() {
		
		@Override
		public final void run() {
			Standard.setup();
			
			{
				final Object _X = $new("X");
				
				suppose("definition_of_parentheses", $forall(_X,
						$(p(_X), "=", _X)));
			}
			
			{
				final Object _x = $new("x");
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("definition_of_subset", $forall(_X, _Y,
						$($(_X, SUBSET, _Y), "=", $forall(_x, $rule($(_x, IN, _X), $(_x, IN, _Y))))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("definition_of_powerset", $forall(_X, _Y,
						$($(_X, IN, pp(_Y)), "=", $(_X, SUBSET, _Y))));
			}
			
			{
				suppose("type_of_P_R", $(pp(R), SUBSET, U));
			}
			
			{
				final Object _x = $new("x");
				final Object _X = $new("X");
				final Object _P = $new("P");
				
				suppose("definition_of_forall_in", $forall(_x, _X, _P,
						$($(FORALL, _x, IN, _X, _P), "=", $forall(_x, $rule($(_x, IN, _X), _P)))));
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _X = $new("X");
				final Object _P = $new("P");
				
				suppose("definition_of_forall_in_2", $forall(_x, _y, _X, _P,
						$($(FORALL, _x, ",", _y, IN, _X, _P), "=", $forall(_x, $rule($(_x, IN, _X), $forall(_y, $rule($(_y, IN, _X), _P)))))));
			}
			
			{
				final Object _x = $new("x");
				final Object _y = $new("y");
				final Object _z = $new("z");
				final Object _X = $new("X");
				final Object _P = $new("P");
				
				suppose("definition_of_forall_in_3", $forall(_x, _y, _X, _P,
						$($(FORALL, _x, ",", _y, ",", _z, IN, _X, _P),
								"=", $forall(_x, $rule($(_x, IN, _X), $forall(_y, $rule($(_y, IN, _X), $forall(_z, $rule($(_z, IN, _X), _P)))))))));
			}
			
			{
				final Object _n = $new("n");
				
				suppose("definition_of_positives", $(FORALL, _n, IN, N,
						$rule($(0, "<", _n), $(_n, IN, POS))));
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
				final Object _j = $new("j");
				
				suppose("type_of_flat",
						$(FORALL, _n, IN, POS,
								$(FORALL, _s, IN, $(POS, "^", _n,
										$forall(_X, $($("flat", " ", $(p(1), "_", $(_i, IN, cartesian(_s, _j, _n)))), IN, $(R, "^", $(PI, _s))))))));
			}
			
			{
				final Object _X = $new("X");
				
				suppose("definition_of_singleton",
						$forall(_X,
								$(_X, IN, c(_X))));
			}
			
			{
				final Object _X = $new("X");
				final Object _x = $new("x");
				
				suppose("type_of_single",
						$forall(_X,
								$(FORALL, _x, IN, _X,
												$(p(_x), IN, _X))));
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
			
			{
				final Object _X = $new("X");
				
				suppose("cartesian_1",
						$(FORALL, _X, IN, U,
								$(_X, "=", $(_X, "^", 1))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				
				suppose("type_of_cartesian",
						$(FORALL, _X, ",", _Y, IN, U,
								$(pp(_X, CROSS, _Y), SUBSET, U)));
			}
			
			{
				final Object _X = $new("X");
				final Object _m = $new("m");
				final Object _n = $new("n");
				
				suppose("cartesian_m_n",
						$(FORALL, _X, IN, U,
								$(FORALL, _m, ",", _n, IN, POS,
										$($($(_X, "^", _m), CROSS, $(_X, "^", _n)), "=", $(_X, "^", $(_m, "+", _n))))));
			}
			
			{
				final Object _X = $new("X");
				final Object _Y = $new("Y");
				final Object _Z = $new("Z");
				
				suppose("cartesian_associativity",
						$(FORALL, _X, ",", _Y, ",", _Z, IN, U,
										$($(p(_X, CROSS, _Y), CROSS, _Z), "=", $(_X, CROSS, p(_Y, CROSS, _Z)))));
			}
		}
		
	}, 1);
	
	public static final ComputationNode ones() {
		final ComputationNode result = new ComputationNode().setTypeName("ones");
		
		final Object n = $new("n");
		final Object s = $new("s");
		final Object i = $new("i");
		
		result.setDefinition(
				$(FORALL, n, IN, POS,
						$(FORALL, s, IN, $(POS, "^", n),
								$($("ones", " ", s), "=", p($(p(1), "_", $(i, "<", $(PI, s))), ",", s)))));
		
		result.set("s", null);
		
		result.getBindListeners().add(new BindListener() {
			
			@Override
			public final void beforeBind(final String key, final Object value) {
				if ("s".equals(key)) {
					final int[] shape = (int[]) value;
					
					NodesTools.check(0 < shape.length, () -> "Invalid shape: []");
					
					result.set("n", shape.length);
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
	
	public static final void deducePositivity(final Object target) {
		subdeduction();
		
		{
			subdeduction();
			
			final Object n = list(proposition("definition_of_positives")).get(1);
			
			bind("definition_of_forall_in", n, N, $rule($(0, "<", n), $(n, IN, POS)));
			rewrite("definition_of_positives", name(-1));
			
			conclude();
		}
		
		bind(name(-1), target);
		verifyBasicNumericProposition($(target, IN, N));
		apply(name(-2), name(-1));
		verifyBasicNumericProposition($(0, "<", target));
		apply(name(-2), name(-1));
		
		conclude();
	}
	
	public static final void canonicalizeForallIn(final String target) {
		final Object proposition = proposition(target);
		
		subdeduction();
		
		bind("definition_of_forall_in", list(proposition).get(1), list(proposition).get(3), list(proposition).get(4));
		rewrite(target, name(-1));
		
		conclude();
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
	
	public static final Object cartesian(final Object _s, final Object _j, final Object _n) {
		return $(CROSS, "_", $(_j, "<", _n), $(N, "_", $("<", $(_s, "_", _j))));
	}
	
	public static final Object pp(final Object... set) {
		return $(P, p(set));
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
