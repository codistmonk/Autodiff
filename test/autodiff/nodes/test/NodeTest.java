package autodiff.nodes.test;

import static autodiff.nodes.ComputationNode.*;
import static autodiff.reasoning.deductions.Standard.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.BasicNumericVerification.*;
import static autodiff.reasoning.proofs.Stack.*;
import static autodiff.rules.PatternPredicate.rule;
import static multij.tools.Tools.debugPrint;
import static multij.tools.Tools.invoke;
import static org.junit.Assert.*;

import autodiff.nodes.ComputationNode;
import autodiff.nodes.ComputationNode.PropositionDescription;
import autodiff.nodes.Data;
import autodiff.nodes.Node;
import autodiff.reasoning.deductions.Standard;
import autodiff.reasoning.expressions.ExpressionRewriter;
import autodiff.reasoning.proofs.Deduction;
import autodiff.rules.PatternPredicate;
import autodiff.rules.Rules;
import autodiff.rules.Variable;

import java.io.Serializable;
import java.nio.ByteBuffer;
import java.nio.ByteOrder;
import java.nio.FloatBuffer;
import java.util.LinkedHashMap;
import java.util.List;
import java.util.Map;

import org.junit.Test;

/**
 * @author codistmonk (creation 2016-07-11)
 */
public final class NodeTest {
	
	@Test
	public final void testShapes1() {
		final Node<?> x = new Data().setShape(1);
		
		assertArrayEquals(new int[] { 1 }, x.getShape());
		
		assertArrayEquals(new int[] { 1 }, x.getLengths(new int [1]));
		assertArrayEquals(new int[] { 1, 1 }, x.getLengths(new int [2]));
	}
	
	@Test
	public final void testShapes2() {
		final Node<?> x = new Data().setShape(2, 3, 4);
		
		assertArrayEquals(new int[] { 2, 3, 4 }, x.getShape());
		
		assertArrayEquals(new int[] { 24 }, x.getLengths(new int [1]));
		assertArrayEquals(new int[] { 2, 12 }, x.getLengths(new int [2]));
		assertArrayEquals(new int[] { 2, 3, 4 }, x.getLengths(new int [3]));
		assertArrayEquals(new int[] { 2, 3, 4, 1 }, x.getLengths(new int [4]));
	}
	
	@Test
	public final void testGetSet1() {
		final Node<?> x = new Data().setShape(1);
		
		x.set(42F);
		
		assertEquals(42.0, x.get(), 0.0);
	}
	
	@Test
	public final void testGetSet2() {
		final Node<?> x = new Data().setShape(2);
		
		x.set(42F, 33F);
		
		assertEquals(42.0, x.get(0), 0.0);
		assertEquals(33.0, x.get(1), 0.0);
	}
	
	@Test
	public final void testComputationNode1() {
		final ComputationNode node = ComputationNode.ones();
		
		node.set("s", new int[] { 2 });
		
		node.autoShape();
		
		assertArrayEquals(new int[] { 2 }, node.getShape());
		
		Standard.build(new Deduction(node.getBoundForm(), node.getName() + "_to_java"), new Runnable() {
			
			@Override
			public final void run() {
				final Object boundForm = proposition(-1);
				final Object valuesExpression = left(middle(right(boundForm)));
				final Object nExpression = right(right(valuesExpression));
				
				debugPrint(valuesExpression);
				debugPrint(nExpression);
				
				{
					subdeduction();
					
					computeVectorReductionByProduct(nExpression);
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				{
					subdeduction();
					
					final Object _n = 2;
					final Object _i = $new("i");
					final Object _X = 1;
					
					ebind("definition_of_vector_generator_to_java", _X, _i, _n);
					eapplyLast();
					
					{
						subdeduction();
						
						final Object j = second(left(proposition(-1)));
						
						{
							subdeduction();
							
							final Object _j = forall("j");
							
							suppose($(_j, IN, $(N, "_", $("<", _n))));
							
							substitute(_X, map(_i, _j));
							
							{
								final Object proposition = $(right(proposition(-1)), IN, R);
								final PropositionDescription justication = justicationFor(proposition);
								
								rewriteRight(justication.getName(), name(-2));
							}
							
							conclude();
						}
						
						{
							ebind("definition_of_forall_in", j, $(N, "_", $("<", _n)), $($(_X, "|", $1($(_i, "=", j)), "@", $()), IN, R));
							
							rewriteRight(name(-2), name(-1));
						}
						
						conclude();
					}
					
					eapply(name(-2));
					
					ebindTrim("definition_of_real_to_java", _X);
					
					rewrite(name(-2), name(-1));
					
					conclude();
				}
				
				{
					final Context context = new Context();
					
					context.setBuffer("result", node.getFloatBuffer());
					
					context.interpret(right(proposition(-1)));
					
					debugPrint(context.read("result", 0), context.read("result", 1));
				}
			}
			
		}, 1);
		
		fail("TODO");
	}
	
	@Test
	public final void testComputationNode2() {
		final ComputationNode node = ComputationNode.ones();
		
		node.set("s", new int[] { 2, 1, 3 });
		
		node.autoShape();
		
		assertArrayEquals(new int[] { 2, 1, 3 }, node.getShape());
		
		fail("TODO");
	}
	
	/**
	 * @author codistmonk (creation 2016-08-16)
	 */
	public static final class Context implements Serializable {
		
		private final Map<String, FloatBuffer> buffers = new LinkedHashMap<>();
		
		private final Interpreter interpreter = this.new Interpreter();
		
		public final Object interpret(final Object program) {
			return this.interpreter.apply(program);
		}
		
		public final void repeat(final Number n, final String counterName, final Number counterIndex, final Runnable instructions) {
			final String deltaName = this.buffers.size() + ":delta";
			
			this.allocate(deltaName, 1);
			this.write(deltaName, 0, 1);
			
			for (this.write(counterName, counterIndex, 0);
					this.read(counterName, counterIndex) < n.intValue();
					this.addTo(counterName, counterIndex, deltaName, 0)) {
				instructions.run();
			}
		}
		
		public final void allocate(final String name, final int n) {
			this.buffers.put(name,
					ByteBuffer.allocateDirect(n * Float.BYTES).order(ByteOrder.nativeOrder()).asFloatBuffer());
		}
		
		public final void write(final String targetName, final Number index, final Number value) {
			this.getBuffer(targetName).put(index.intValue(), value.floatValue());
		}
		
		public final float read(final String sourceName, final Number index) {
			return this.getBuffer(sourceName).get(index.intValue());
		}
		
		public final void addTo(final String targetName, final Number targetIndex, final String sourceName, final Number sourceIndex) {
			this.write(targetName, targetIndex,
					this.read(targetName, targetIndex) + this.read(sourceName, sourceIndex));
		}
		
		public final FloatBuffer getBuffer(final String name) {
			return this.buffers.get(name);
		}
		
		public final void setBuffer(final String name, final FloatBuffer buffer) {
			this.buffers.put(name, buffer);
		}
		
		/**
		 * @author codistmonk (creation 2016-08-16)
		 */
		public final class Interpreter implements ExpressionRewriter {
			
			private final Rules<Object, Object> rules = new Rules<>();
			
			{
				{
					final Variable s = new Variable("s");
					
					this.rules.add(rule($("\"", s, "\""), (__, m) -> m.get(s).toString()));
				}
				
				{
					final Variable p = new Variable("p");
					
					this.rules.add(rule($("()->{", p, "}"), (__, m) -> new Runnable() {
						
						private final Object _p = m.get(p);
						
						@Override
						public final void run() {
							Interpreter.this.apply(this._p);
						}
						
					}));
				}
				
				{
					final Variable f = new Variable("f");
					final Variable x = new Variable("x");
					
					this.rules.add(rule($(f, "(", x, ")"), (__, m) -> {
						final List<Object> arguments = flattenSequence(",", this.apply(m.get(x)));
						
						return invoke(Context.this, m.get(f).toString(), arguments.toArray());
					}));
				}
				
				{
					this.rules.add(rule(new Variable("*"), (e, __) -> ExpressionRewriter.super.visit((List<?>) e)));
				}
			}
			
			@Override
			public final Object visit(final List<?> expression) {
				return this.rules.applyTo(expression);
			}
			
			private static final long serialVersionUID = -6614888521968958004L;
			
		}
		
		private static final long serialVersionUID = -7818200319668460156L;
		
	}
	
}
