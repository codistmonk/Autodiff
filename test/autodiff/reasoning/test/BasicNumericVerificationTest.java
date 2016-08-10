package autodiff.reasoning.test;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.BasicNumericVerification.*;
import static autodiff.reasoning.proofs.Stack.*;

import org.junit.Test;

import autodiff.reasoning.proofs.BasicNumericVerification.BinaryOperator;

/**
 * @author codistmonk (creation 2016-01-30)
 */
public final class BasicNumericVerificationTest {
	
	@Test
	public final void testOK1() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				verifyBasicNumericProposition($(2, BinaryOperator.EQUAL, 2));
				verifyBasicNumericProposition($equality(2, 2));
				verifyBasicNumericProposition($equality($(1, "+", 1), 2));
				verifyBasicNumericProposition($equality(2, $(1, "+", 1)));
				verifyBasicNumericProposition($equality($(2, "+", 4), $(3, "*", 2)));
				verifyBasicNumericProposition($equality($(2, "/", 4), $(0.5)));
				verifyBasicNumericProposition($equality($("abs", -2), 2));
				verifyBasicNumericProposition($equality($("floor", $(2, "/", 4)), $(0)));
				verifyBasicNumericProposition($equality($("ceiling", $(2, "/", 4)), $(1)));
			}
			
		});
	}
	
	@Test
	public final void testOK2() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				verifyBasicNumericProposition($(2, "∈", N));
				verifyBasicNumericProposition($(2, "∈", Z));
				verifyBasicNumericProposition($(2, "∈", Q));
				verifyBasicNumericProposition($(2, "∈", R));
				verifyBasicNumericProposition($(-2, "∈", Z));
				verifyBasicNumericProposition($(-2, "∈", Q));
				verifyBasicNumericProposition($(-2, "∈", R));
				verifyBasicNumericProposition($(2.5, "∈", Q));
				verifyBasicNumericProposition($(2.5, "∈", R));
			}
			
		});
	}
	
	@Test(expected=Exception.class)
	public final void testKO1() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				verifyBasicNumericProposition($equality(2, 3));
			}
			
		});
	}
	
	@Test(expected=Exception.class)
	public final void testKO2() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				verifyBasicNumericProposition($equality(1, "1"));
			}
			
		});
	}
	
	@Test(expected=Exception.class)
	public final void testKO3() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				verifyBasicNumericProposition($(2.5, "∈", N));
			}
			
		});
	}
	
}
