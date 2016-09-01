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
			this.println("<link rel=\"stylesheet\" href=\"lib/js/jQuery-UI/jquery-ui.min.css\"></link>");
			this.println("<script type=\"text/x-mathjax-config\">");
			this.println("  MathJax.Hub.Config({");
			this.println("    extensions: [\"tex2jax.js\"],");
			this.println("    jax: [\"input/TeX\",\"output/HTML-CSS\"],");
			this.println("    tex2jax: {inlineMath: [[\"$\",\"$\"],[\"\\(\",\"\\)\"]]}");
			this.println("  });");
			this.println("</script>");
			this.println("<script type=\"text/javascript\" src=\"lib/js/jQuery/jquery-3.1.0.min.js\"></script>");
			this.println("<script type=\"text/javascript\" src=\"lib/js/jQuery-UI/jquery-ui.min.js\"></script>");
			this.println("<script type=\"text/javascript\" src=\"lib/js/MathJax/MathJax.js\"></script>");
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
			this.println("<script>");
			this.println("  $( function() {");
			this.println("    $( \".accordion\" ).accordion({");
			this.println("      collapsible: true,");
			this.println("      active: false,");
			this.println("      heightStyle: \"content\"");
			this.println("    });");
			this.println("  } );");
			this.println("</script>");
			this.println("</head>");
			this.println("<body>");
			this.println("<blockquote>");
			this.println("<h1>Deduction</h1>");
			this.println("<div class=\"accordion\">");
		}
		
		this.process(deduction.getProvedPropositionName(), "", deduction);
		
		--this.depth;
		
		if (this.depth == 0) {
			this.println("</div>");
			this.println("</blockquote>");
			this.println("</body>");
			this.println("</html>");
		}
	}
	
	private final void process(final String propositionName, final Object proposition, final Proof proof) {
		this.println("<div>");
		this.println("<span>" + propositionName + "</span>");
		this.println("<p style=\"text-align: center\">" + proposition + "</p>");
		this.println("</div>");
		this.println("<div class=\"accordion\">");
		
		this.println("<h2>" + proof.getMessage() + "</h2>");
		this.println("<div>");
		
		{
			final Deduction deduction = Tools.cast(Deduction.class, proof);
			
			if (deduction != null) {
				if (!deduction.getParameters().isEmpty()) {
					this.println("<h3 style=\"text-align: center\">" + FORALL + deduction.getParameters() + "</h3>");
					this.println("<div></div>");
				}
				
				if (!deduction.getConditionNames().isEmpty()) {
					this.println("<h3 style=\"text-align: center\">Conditions</h3>");
					this.println("<div>");
					this.println("</div>");
					
					for (final String name : deduction.getConditionNames()) {
						this.println("<div>");
						this.println("<span>" + name + "</span>");
						this.println("<p style=\"text-align: center\">" + deduction.getProposition(name) + "</p>");
						this.println("</div>");
						this.println("<div></div>");
					}
				}
				
				this.println("<h3 style=\"text-align: center\">Conclusions</h3>");
				this.println("<div class=\"accordion\">");
				
				for (final String name : deduction.getConclusionNames()) {
					this.process(name, deduction.getProposition(name), deduction.getProofs().get(name));
				}
				
				this.println("</div>");
			}
		}
		
		this.println("</div>");
		
		this.println("</div>");
	}
	
	private final void println(final String text) {
		this.getOutput().println(text);
	}
	
	private static final long serialVersionUID = -1397544656843468589L;
	
}
