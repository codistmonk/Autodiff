package autodiff.nodes.test;

import static autodiff.nodes.ComputationNode.*;
import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.Stack.*;
import static multij.tools.Tools.debugPrint;
import static org.junit.Assert.*;

import java.util.List;

import autodiff.nodes.ComputationNode;
import autodiff.nodes.Data;
import autodiff.nodes.Node;
import autodiff.reasoning.deductions.Standard;
import multij.tools.Tools;

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
		
		Standard.build(node.getBoundForm(), new Runnable() {
			
			@Override
			public final void run() {
				final Object boundForm = proposition(-1);
				final Object valuesExpression = left(middle(right(boundForm)));
				final Object nExpression = right(right(valuesExpression));
				final Object v = list(nExpression).get(1);
				
				debugPrint(valuesExpression);
				debugPrint(nExpression);
				
				{
					subdeduction();
					
					ebind("definition_of_product_reduction", 1, v);
					deduceCartesianType(new Object[] { 2 }, "realness");
					eapply(name(-2));
					
					conclude();
				}
				
				{
					final List<?> product = list(right(proposition(-1)));
					final Object i = left(product.get(2));
					final Object operand = product.get(3);
					
					debugPrint(product);
					debugPrint(i, operand);
					
					ebind("definition_of_product_loop_n", 1, i, operand);
				}
				
				abort();
				
				// TODO
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
	
}
