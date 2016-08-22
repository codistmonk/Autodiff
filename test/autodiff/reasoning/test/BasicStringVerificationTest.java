package autodiff.reasoning.test;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.BasicStringVerification.*;
import static autodiff.reasoning.proofs.Stack.*;

import autodiff.reasoning.proofs.BasicStringVerification.BinaryOperator;

import org.junit.Assert;
import org.junit.Test;

/**
 * @author codistmonk (creation 2016-01-30)
 */
public final class BasicStringVerificationTest {
	
	@Test
	public final void testOK1() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				verifyBasicStringProposition($equality($("1", BinaryOperator.ADD, "1"), "11"));
				verifyBasicStringProposition($equality($("1", "+", 2), "12"));
				verifyBasicNumericProposition($equality($("length", "12"), 2));
			}
			
		});
	}
	
	@Test
	public final void testOK2() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				verifyBasicStringProposition($("123", "∈", S));
			}
			
		});
	}
	
	@Test
	public final void testKO1() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				final Object proposition = $equality("2", "3");
				
				verifyBasicStringProposition(proposition);
				
				Assert.assertEquals($(LNOT, proposition), proposition(-1));
			}
			
		});
	}
	
	@Test
	public final void testKO2() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				final Object proposition = $equality(1, "1");
				
				verifyBasicNumericProposition(proposition);
				
				Assert.assertEquals($(LNOT, proposition), proposition(-1));
			}
			
		});
	}
	
	@Test
	public final void testKO3() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				final Object proposition = $(2.5, "∈", S);
				
				verifyBasicStringProposition(proposition);
				
				Assert.assertEquals($(LNOT, proposition), proposition(-1));
			}
			
		});
	}
	
}
