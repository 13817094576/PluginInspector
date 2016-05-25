package ConfigurationPattern;
/***
 * 确认函数是否会抛出某一个exception
 * @author zxl
 *
 */
public class ExceptionContain extends ConfigurationPattern{
	private Exception exceptionValue;
	
	public ExceptionContain(Exception e){
		exceptionValue=e;
	}

	public Exception getExceptionValue(){
		return this.exceptionValue;
	}
	
	public String toString(){
		return this.exceptionValue.toString();
	}
}
