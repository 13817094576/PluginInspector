package AssignmentPattern;
/**
 * Range,��Χ��
 * Range(a,b)Ŀǰֻ֧��a��b��Ϊint����ָ��a��b֮�������intֵ���Ұ���a��b
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
