package tag;

import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

public class BooleanTag implements Tag{
	
	private String name;
	private boolean value;
	public BooleanTag(String name,boolean value){
		this.name=name;
		this.value=value;
	}
	public BooleanTag(boolean value){
		this.name="HasBody";
		this.value=value;
	}

	
	public String getName() {
		return this.name;
	}

	public byte[] getValue() throws AttributeValueException {
		return null;
	}
	public boolean getBooleanValue() throws AttributeValueException{
		return this.value;
	}
}
