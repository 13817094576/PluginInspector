package tag;

import soot.tagkit.AttributeValueException;
import soot.tagkit.Tag;

/**
 * 
 * @author zxl
 *
 *use a int-type Tag to tag all units before analysis.
 *ÿһ��unit����Ψһһ��intֵ��֮��Ӧ
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
