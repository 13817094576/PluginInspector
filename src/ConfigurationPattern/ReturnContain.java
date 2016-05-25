package ConfigurationPattern;
/**
 * 确认函数的返回值是否包含某个值，目前只限于检测boolean（true或 false）
 * @author zxl
 *
 */
public class ReturnContain extends ConfigurationPattern{
	private boolean booleanValue;
	
	private boolean isMust=false;
	private int mode=-1;
	
	private String PROP_MUST="must";
	public ReturnContain(Object v){
		if(v instanceof Boolean){
			booleanValue=(boolean)(v);
			mode=1;
		}
	}
	public ReturnContain(Object v,String string){
		if(v instanceof Boolean){
			booleanValue=(boolean)(v);
			mode=1;
			if(string.equals(PROP_MUST))
				this.isMust=true;
		}
	}
	public Object getReturnValue(){
		switch(mode){
		case 1: return booleanValue;
		}
		return null;
	}
	
	public String toString(){
		return getReturnValue().toString();
	}
	
	public boolean isMust(){
		return this.isMust;
	}
}
