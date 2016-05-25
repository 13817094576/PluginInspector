package tag;

import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

/**
 * 
 * @author zxl
 *
 *use a string-type Tag to tag all units before analysis.
 *
 */

public class StringTag implements Tag{
	private String name;
	private String value;
	public StringTag(String name,String value){
		this.name=name;
		this.value=value;
	}
	public StringTag(String value){
		this.name="StringTag";
		this.value=value;
	}

	
	public String getName() {
		return this.name;
	}

	@Override
	public byte[] getValue() throws AttributeValueException {
		return this.value.getBytes();
	}
	

}
