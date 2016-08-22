package autodiff.reasoning.test;

import static autodiff.reasoning.expressions.Expressions.*;
import static autodiff.reasoning.proofs.ElementaryVerification.*;
import static autodiff.reasoning.proofs.Stack.*;

import org.junit.Assert;
import org.junit.Test;

/**
 * @author codistmonk (creation 2016-01-30)
 */
public final class ElementaryVerificationTest {
	
	@Test
	public final void testOK1() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				verifyElementaryProposition($(2, "=", 2));
				verifyElementaryProposition($equality(2, 2));
				verifyElementaryProposition($equality($(1, "+", 1), 2));
				verifyElementaryProposition($equality(2, $(1, "+", 1)));
				verifyElementaryProposition($equality($(2, "+", 4), $(3, "*", 2)));
				verifyElementaryProposition($equality($(2, "/", 4), $(0.5)));
				verifyElementaryProposition($equality(norm(-2), 2));
				verifyElementaryProposition($equality($("floor", $(2, "/", 4)), $(0)));
				verifyElementaryProposition($equality($("ceiling", $(2, "/", 4)), $(1)));
				verifyElementaryProposition($equality(9, $(3, "^", 2)));
				
				verifyElementaryProposition($equality(2, $(5, "%", 3)));
				verifyElementaryProposition($equality(4, $(2, "<<", 1)));
				verifyElementaryProposition($equality(2, $(4, ">>", 1)));
				verifyElementaryProposition($equality(3, $(2, "|", 1)));
				verifyElementaryProposition($equality(2, $(3, "&", 2)));
				verifyElementaryProposition($equality(1, $(3, "¨", 2)));
				
				verifyElementaryProposition($(LNOT, $(3, "<", 2)));
				verifyElementaryProposition($(2, "<", 3));
				verifyElementaryProposition($(2, "<=", 3));
				verifyElementaryProposition($(2, LE, 3));
				verifyElementaryProposition($(3, ">=", 2));
				verifyElementaryProposition($(3, GE, 2));
				verifyElementaryProposition($(3, ">", 2));
				
				verifyElementaryProposition($equality($("1", "+", "1"), "11"));
				verifyElementaryProposition($equality($("1", "+", 2), "12"));
				verifyElementaryProposition($equality(norm("12"), 2));
			}
			
		});
	}
	
	@Test
	public final void testOK2() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				verifyElementaryProposition($(2, "∈", N));
				verifyElementaryProposition($(2, "∈", Z));
				verifyElementaryProposition($(2, "∈", Q));
				verifyElementaryProposition($(2, "∈", R));
				verifyElementaryProposition($(-2, "∈", Z));
				verifyElementaryProposition($(-2, "∈", Q));
				verifyElementaryProposition($(-2, "∈", R));
				verifyElementaryProposition($(2.5, "∈", Q));
				verifyElementaryProposition($(2.5, "∈", R));
				
				verifyElementaryProposition($("123", "∈", STRING));
			}
			
		});
	}
	
	@Test
	public final void testKO1() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				final Object proposition = $equality(2, 3);
				
				verifyElementaryProposition(proposition);
				
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
				
				verifyElementaryProposition(proposition);
				
				Assert.assertEquals($(LNOT, proposition), proposition(-1));
			}
			
		});
	}
	
	@Test
	public final void testKO3() {
		StandardTest.build(new Runnable() {
			
			@Override
			public final void run() {
				final Object proposition = $(2.5, "∈", N);
				
				verifyElementaryProposition(proposition);
				
				Assert.assertEquals($(LNOT, proposition), proposition(-1));
			}
			
		});
	}
	
}
