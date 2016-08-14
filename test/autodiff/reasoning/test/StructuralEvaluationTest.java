package autodiff.reasoning.test;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.Stack.*;
import static autodiff.reasoning.proofs.StructuralEvaluation.MATCH;

import org.junit.Assert;
import org.junit.Test;

/**
 * @author codistmonk (creation 2016-08-14)
 */
public final class StructuralEvaluationTest {
	
	@Test
	public final void test1() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				{
					final Object proposition = $(2, MATCH, 2);
					
					evaluateStructuralFormula(proposition);
					
					Assert.assertEquals($(proposition, "=", true), proposition(-1));
				}
				
				{
					final Object proposition = $(2, MATCH, 3);
					
					evaluateStructuralFormula(proposition);
					
					Assert.assertEquals($(proposition, "=", false), proposition(-1));
				}
			}
			
		});
	}
	
}
