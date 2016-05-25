package ConfigurationPattern;

import java.util.Iterator;

import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SootMethod;

public class MethodContain  extends ConfigurationPattern {
	
	private String signature;
	public MethodContain(String s){
		signature=s;
	}
	
	public String getSignature(){
		return signature;
	}
	public SootMethod getMethod(){
		for(Iterator<MethodOrMethodContext> iter = Scene.v().getReachableMethods().listener(); iter.hasNext();){
			SootMethod m=iter.next().method();
			if(m.getSignature().equals(signature))
				return m;
		}
		return null;
	}
	public String toString(){
		return signature;
	}
}
