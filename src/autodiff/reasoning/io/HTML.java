package autodiff.reasoning.io;

import static autodiff.reasoning.expressions.Expressions.FORALL;

import java.io.PrintStream;

import autodiff.reasoning.proofs.Deduction;
import autodiff.reasoning.proofs.Proof;

import multij.tools.Tools;

/**
 * @author codistmonk (creation 2016-08-31)
 */
public final class HTML implements Deduction.Processor {
	
	private PrintStream output = System.out;
	
	private int depth = -1;
	
	public final PrintStream getOutput() {
		return this.output;
	}
	
	public final HTML setOutput(final PrintStream output) {
		this.output = output;
		
		return this;
	}
	
	@Override
	public final void process(final Deduction deduction) {
		++this.depth;
		
		if (this.depth == 0) {
			this.println("<!DOCTYPE html>");
			this.println("<html>");
			this.println("<head>");
			this.println("<title>MathJax Test Page</title>");
			this.println("<meta http-equiv=\"Content-Type\" content=\"text/html; charset=UTF-8\" />");
			this.println("<meta http-equiv=\"X-UA-Compatible\" content=\"IE=edge\" />");
			this.println("<meta name=\"viewport\" content=\"width=device-width, initial-scale=1\" />");
			this.println("<script type=\"text/x-mathjax-config\">");
			this.println("  MathJax.Hub.Config({");
			this.println("    extensions: [\"tex2jax.js\"],");
			this.println("    jax: [\"input/TeX\",\"output/HTML-CSS\"],");
			this.println("    tex2jax: {inlineMath: [[\"$\",\"$\"],[\"\\(\",\"\\)\"]]}");
			this.println("  });");
			this.println("</script>");
			this.println("<script type=\"text/javascript\" src=\"../lib/MathJax/MathJax.js\"></script>");
			this.println("<style>");
			this.println("h1 {text-align:center}");
			this.println("h2 {");
			this.println("  font-weight: bold;");
			this.println("  background-color: #DDDDDD;");
			this.println("  padding: .2em .5em;");
			this.println("  margin-top: 1.5em;");
			this.println("  border-top: 3px solid #666666;");
			this.println("  border-bottom: 2px solid #999999;");
			this.println("}");
			this.println("</style>");
			this.println("</head>");
			this.println("<body>");
			this.println("<blockquote>");
		}
		
		this.process(deduction.getProvedPropositionName(), "", deduction);
		
		--this.depth;
		
		if (this.depth == 0) {
			this.println("</blockquote>");
			this.println("</body>");
			this.println("</html>");
		}
	}
	
	private final void process(final String propositionName, final Object proposition, final Proof proof) {
		this.println("<h2>" + propositionName + "</h2>");
		this.println("<div>");
		
		this.println("<p>" + proposition + "</p>");
		this.println("<p>" + proof.getMessage() + "</p>");
		
		{
			final Deduction deduction = Tools.cast(Deduction.class, proof);
			
			if (deduction != null) {
				if (!deduction.getParameters().isEmpty()) {
					this.println("<p>" + FORALL + deduction.getParameters() + "</p>");
				}
				
				for (final String name : deduction.getConditionNames()) {
					this.println("<h2>" + name + "</h2>");
					this.println("<p>" + deduction.getProposition(name) + "</p>");
				}
				
				for (final String name : deduction.getConclusionNames()) {
					this.process(name, deduction.getProposition(name), deduction.getProofs().get(name));
				}
			}
		}
		
		this.println("</div>");
	}
	
	private final void println(final String text) {
		this.getOutput().println(text);
	}
	
	private static final long serialVersionUID = -1397544656843468589L;
	
}
