package AssignmentPattern;

import java.util.regex.Pattern;
/*
 * mathch ��ָ Assignment��Ĳ���Ҫ����ĳһ��������ʽ����������ʽ��match����
 * */

public class Match{
	private String pattern;
	
	public Match(String str){
		this.pattern=str;
	}
	
	public Pattern getPattern(){
		Pattern matchPattern=Pattern.compile(this.pattern);
		return matchPattern;
		
	}
}
