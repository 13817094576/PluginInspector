package ConfigurationPattern;
/***
 * ȷ�Ϻ����Ƿ���׳�ĳһ��exception
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
