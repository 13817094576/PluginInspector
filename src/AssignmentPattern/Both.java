package AssignmentPattern;

public class Both {
	
	private Not not1;
	private Not not2;
	
	String mode=null;
	public Both(Object v1,Object v2){
		if(v1 instanceof Not && v2 instanceof Not){
			not1=(Not)v1;
			not2=(Not)v2;
			mode="not";
		}
	}
	
	public String getMode(){
		return mode;
	}
	public Object getValue1(){
		if(mode==null) return null;
		switch(mode){
			case "not": return not1;
		}
		return null;
	}
	public Object getValue2(){
		if(mode==null) return null;
		switch(mode){
			case "not": return not2;
		}
		return null;
	}
}
