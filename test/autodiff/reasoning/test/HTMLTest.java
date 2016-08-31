package autodiff.reasoning.test;

import autodiff.reasoning.deductions.Basics;
import autodiff.reasoning.io.HTML;
import autodiff.reasoning.proofs.Deduction;

import java.io.FileNotFoundException;
import java.io.PrintStream;

import org.junit.Test;

/**
 * @author codistmonk (creation 2016-08-31)
 */
public final class HTMLTest {
	
	@Test
	public final void test1() throws FileNotFoundException {
		final HTML printer = new HTML().setOutput(new PrintStream("index.html"));
		final Deduction deduction = BasicsTest.build(() -> {
			Basics.load();
		}, printer);
		
		printer.process(deduction);
	}
	
}
