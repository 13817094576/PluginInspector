package tipsticker;

import java.util.HashSet;
import java.util.Set;

public class test {

	public static void main(String[] args) {
		// TODO Auto-generated method stub
//		Pattern p1=Pattern.compile("^http:.*");
//		Pattern p2=Pattern.compile("file:[/]{2,3}[^/]*(?=assets/).*|file:[/]{2,3}[^/]*(?=rets/).*");
//		String s1="http://127.0.0.1";
//		String s2="https://127.0.0.1.1";
//		String s3="file:///android-assets/a/b/c";
//		String s4="file://android-rets/a/b";
//		String s5="fie://android-rets/a/b";
//		System.out.println(p1.matcher(s1).matches());
//		System.out.println(p1.matcher(s2).matches());
//		System.out.println(p2.matcher(s3).matches());
//		System.out.println(p2.matcher(s4).matches());
//		System.out.println(p2.matcher(s5).matches());
		
		Set<String> s1=new HashSet<String>();
		s1.add("hello");
		System.out.println(s1);
		s1.add("world");
		System.out.println(s1);
		Set<String> s2=new HashSet<String>();
		s2.addAll(s1);
		System.out.println(s2);
		s2.addAll(s1);
		System.out.println(s2);

	}

}
