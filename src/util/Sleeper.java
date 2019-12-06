package util;

import io.usethesource.vallang.IInteger;
import io.usethesource.vallang.IValueFactory;

public class Sleeper {

	public Sleeper(IValueFactory vf) {}
	
	public void sleep(IInteger ms) {
		try {
			Thread.sleep(ms.longValue());
		} catch (InterruptedException e) { 
			e.printStackTrace();
		}		
	}
}
