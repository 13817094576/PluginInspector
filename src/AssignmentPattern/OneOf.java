package AssignmentPattern;
/**
 * oneOf,即之一，oneOf（pattern1，pattern2）就是指只需要满足pattern1或pattern2就可
 * 目前，这里的pattern还只是AssignmentPattern，以后可拓展支持ConfigurationPattern
 * 
 * */
public class OneOf {
	private int intNum1;
	private int intNum2;
	private String str1;
	private String str2;
	private Match match1;
	private Match match2;
	private Range range1;
	private Range range2;
	
	private int[] intList;
	
	private int mode=0;
	
	public OneOf(Object v1,Object v2){
		if((v1 instanceof Integer)&&(v2 instanceof Integer)){
			this.intNum1=(int)v1;
			this.intNum2=(int)v2;
			this.mode=1;
		}
		else if((v1 instanceof String)&&(v2 instanceof String)){
			this.str1=(String)v1;
			this.str2=(String)v2;
			this.mode=2;
		}
		else if((v1 instanceof Match)&&(v2 instanceof Match)){
			this.match1=(Match)v1;
			this.match2=(Match)v2;
			this.mode=3;
		}
		else if((v1 instanceof Range)&&(v2 instanceof Range)){
			this.range1=(Range)v1;
			this.range2=(Range)v2;
			this.mode=4;
		}
	}
	public OneOf(int[] list){
		intList=list;
		mode=5;
	}
	
	public int getMode(){
		return this.mode;
	}
	public int getInt(int index){
		if(index==1)
			return this.intNum1;
		else
			if(index==2)
				return this.intNum2;
		return 0;
	}
	public String getString(int index){
		if(index==1)
			return this.str1;
		else if(index==2)
			return this.str2;
		return null;
	}
	public Match getMatch(int index){
		if(index==1)
			return this.match1;
		else if(index==2)
			return this.match2;
		return null;
	}
	public Range getRange(int index){
		if(index==1)
			return this.range1;
		else if(index==2)
			return this.range2;
		return null;
	}
	public int[] getIntList(){
		return intList;
	}
	
	
}
