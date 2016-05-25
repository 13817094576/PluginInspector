package AssignmentPattern;

import ConfigurationPattern.ExceptionContain;
import ConfigurationPattern.MethodContain;
import ConfigurationPattern.ReturnContain;
/**
 * not 一般是对结果取非，例如，Not（pattern）就是指不满足pattern的时候
 * pattern适用于AssignmentPattern和ConfigurationPattern
 * @author zxl
 *
 */
public class Not {
	
	private int intValue;
	private String stringValue;
	private Match matchValue;
	private OneOf oneOfValue;
	private Range rangeValue;
	
	private ExceptionContain exceptionContain;
	private ReturnContain returnContain;
	private MethodContain methodContain;
	private int mode=-1;
	
	public Not(Object v){
		if(v instanceof Integer){
			mode=1;
			intValue=(int)v;
		}
		else if(v instanceof String){
			mode=2;
			stringValue=(String)v;
		}
		else if(v instanceof Match){
			mode=3;
			matchValue=(Match)v;
		}
		else if(v instanceof OneOf){
			mode=4;
			oneOfValue=(OneOf)v;
		}
		else if(v instanceof Range){
			mode=5;
			rangeValue=(Range)v;
		}
		else if(v instanceof ExceptionContain){
			this.mode=11;
			this.exceptionContain=(ExceptionContain)v;
		}
		else if(v instanceof ReturnContain){
			this.mode=12;
			this.returnContain=(ReturnContain)v;
		}
		else if(v instanceof MethodContain){
			mode=13;
			methodContain=(MethodContain)v;
		}
	}
	
	public Object getValue(){
		switch(mode){
		case 1: return intValue;
		case 2: return stringValue;
		case 3: return matchValue;
		case 4: return oneOfValue;
		case 5: return rangeValue;
		
		case 11:return exceptionContain;
		case 12:return returnContain;
		case 13:return methodContain;
		}
		return null;
	}
	
	public int getMode(){
		return this.mode;
	}
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
	
}
