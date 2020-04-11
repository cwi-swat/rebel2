package salix.lib;

import java.io.ByteArrayOutputStream;
import java.io.IOException;
import java.nio.charset.Charset;

import org.rascalmpl.interpreter.utils.RuntimeExceptionFactory;

import io.usethesource.vallang.IString;
import io.usethesource.vallang.IValueFactory;
import net.sourceforge.plantuml.FileFormat;
import net.sourceforge.plantuml.FileFormatOption;
import net.sourceforge.plantuml.SourceStringReader;

public class PlantUML {

	private IValueFactory vf;
	
	public PlantUML(IValueFactory factory) {
		this.vf = factory;
	}
	
	public IString uml2svg(IString src) {
		String source = src.getValue();
		SourceStringReader reader = new SourceStringReader(source);
		final ByteArrayOutputStream os = new ByteArrayOutputStream();
		// Write the first image to "os"
		try {
			String img = reader.outputImage(os, new FileFormatOption(FileFormat.SVG)).getDescription();
			System.out.println(img);
			os.close();
			return vf.string(new String(os.toByteArray(), Charset.forName("UTF-8")));

		} catch (IOException e) {
			throw RuntimeExceptionFactory.io(vf.string(e.getMessage()), null, null);
		}
	}
}
