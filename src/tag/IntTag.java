package tag;

import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

/**
 * 
 * @author zxl
 *
 *use a int-type Tag to tag all units before analysis.
 *每一个unit都有唯一一个int值与之对应
 */

public class IntTag implements Tag{
	private String name;
	private int value;
	public IntTag(String name,int value){
		this.name=name;
		this.value=value;
	}
	public IntTag(int value){
		this.name="IntTag";
		this.value=value;
	}

	
	public String getName() {
		return this.name;
	}

	@Override
	public byte[] getValue() throws AttributeValueException {
		return null;
	}
	public int getIntValue() throws AttributeValueException{
		return this.value;
	}

}
