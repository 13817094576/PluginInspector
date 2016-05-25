package AssignmentPattern;
/**
 * Range,范围。
 * Range(a,b)目前只支持a和b均为int，是指从a到b之间的所有int值，且包含a和b
 * 
 * 
 * **/
public class Range {
	private int startNum;
	private int endNum;
	
	public Range(String str){
		String arr[]=str.split("-");
		this.startNum=Integer.parseInt(arr[0]);
		this.endNum=Integer.parseInt(arr[1]);
	}
	public int getStart(){
		return this.startNum;
	}
	public int getEnd(){
		return this.endNum;
	}
}
