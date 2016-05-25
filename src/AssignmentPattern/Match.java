package AssignmentPattern;

import java.util.regex.Pattern;
/*
 * mathch 是指 Assignment里的参数要满足某一种正则表达式，该正则表达式由match给出
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
