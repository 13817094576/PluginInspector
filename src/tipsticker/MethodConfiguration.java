package tipsticker;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import soot.FastHierarchy;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Type;
import soot.Unit;
import soot.jimple.Stmt;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JThrowStmt;
import AssignmentPattern.Both;
import AssignmentPattern.Not;
import ConfigurationPattern.ExceptionContain;
import ConfigurationPattern.MethodContain;
import ConfigurationPattern.ReturnContain;
/**
 * MethodConfiguration主要用来判断某个函数是否具有某种功能或属性，或者说是否满足某种pattern
 * @author zxl
 *
 */
public class MethodConfiguration extends Configuration{
	private String signature;
	
	private SootMethod method;
	private List<String> exception;
	private Type retType;
	
	private int mode=-1;
	private ExceptionContain exceptionContain;//可以抛出某种exception
	private ReturnContain returnContain;//可以返回某个值
	private MethodContain methodContain;
	private Not not;
	private Both both;
	private boolean unsafeMethodCall=false; //如果被调用了，就是unsafe
	private boolean isHierarchy=false;
	private String UnsafeMethodCall="unsafeMethodCall";
	private String Hierarchy="hierarchy";
	
	MethodConfiguration(String signature,Object pattern){
		method=getMethod(signature);
		this.signature=signature;
		if(method!=null){
			exception=getExceptions();
			retType=method.getReturnType();
		}
		if(pattern instanceof ExceptionContain){
			mode=1;
			exceptionContain=(ExceptionContain)pattern;
		}
		else if(pattern instanceof ReturnContain){
			mode=2;
			returnContain=(ReturnContain)pattern;
		}
		else if(pattern instanceof Not){
			mode=3;
			not=(Not)pattern;
		}
		else if(pattern instanceof String && pattern.equals(UnsafeMethodCall)){
			mode=4;
			unsafeMethodCall=true;
		}
		else if(pattern instanceof MethodContain){
			mode=5;
			methodContain=(MethodContain)pattern;
		}
		else if(pattern instanceof Both){
			mode=6;
			both=(Both)pattern;
		}
	}
	MethodConfiguration(String signature,Object pattern,String hierarchy){
		this(signature,pattern);
		if(hierarchy.equals(Hierarchy)){
			isHierarchy=true;
		}
	}
	public MethodConfiguration() {
		// TODO Auto-generated constructor stub
	}
	/**
	 * 该函数是为了分析deadcode的影响，可以忽略
	 * @param signature
	 * @param pattern
	 * @param hierarchy
	 */
	public void MethodConfigurationIncludingDeadCode(String signature,Object pattern,String hierarchy){
		this.setRuleName("SSL_v1_includingDeadCode");
		method=getMethod_includingDeadCode(signature);
		this.signature=signature;
		isHierarchy=hierarchy.equals(Hierarchy);
		unsafeMethodCall=false;
		if(method!=null){
			exception=getExceptions();
			retType=method.getReturnType();
		}
		if(pattern instanceof ExceptionContain){
			mode=1;
			exceptionContain=(ExceptionContain)pattern;
		}
		else if(pattern instanceof ReturnContain){
			mode=2;
			returnContain=(ReturnContain)pattern;
		}
		else if(pattern instanceof Not){
			mode=3;
			not=(Not)pattern;
		}
		else if(pattern instanceof String && pattern.equals(UnsafeMethodCall)){
			mode=4;
			unsafeMethodCall=true;
		}
		configurationAnalysis();
	}
	private SootMethod getMethod(String signature){
		if(signature.contains("onGeolocationPermissionsShowPrompt")){
			for(SootClass sootClass:Scene.v().getClasses()){
				for(SootMethod m:sootClass.getMethods())
					if(m.getSignature().contains("onGeolocationPermissionsShowPrompt"))
					if(m.getSignature().equals(signature))
						return m;
				}
		}
		for (Iterator<MethodOrMethodContext> iter = Scene.v().getReachableMethods().listener(); iter.hasNext();) {
			SootMethod m = iter.next().method();
			if(m.getSignature().equals(signature)){
				return m;
			}
		}
		return null;
	}
	private SootMethod getMethod_includingDeadCode(String signature){
		for(SootClass c:Scene.v().getClasses())
			for(SootMethod m:c.getMethods())
				if(m.getSignature()==signature)
					return m;
		return null;
	}
	public Object getPattern(){
		switch(mode){
		case 1:return exceptionContain;
		case 2:return returnContain;
		case 3:return not;
		case 4:return UnsafeMethodCall;
		case 5:return methodContain;
		case 6:return both;
		}
		return null;
	}
	public String getSignature(){
		return this.signature;
	}
	public SootMethod getSootMethod(){
		return this.method;
	}
	public Type getReturnType(){
		return this.retType;
	}
	public List<String> getException(){
		return this.exception;
	}
	
	public boolean configurationAnalysis(){
		boolean result=false;
		boolean set=true;
//		for(String unsafe:Main.unsafeConfiguration){
//			if(unsafe.contains(signature))
//				set=false;
//		}
		if(set&&method!=null)
		switch(mode){
		case 1:if(exceptionContainAnalysis()){
				Main.unsafeConfiguration.add(((Rule)(this)).getRuleName()+" "+signature+" throws exception: "+exceptionContain);
				result=true;
				}
				break;
		case 2:if(returnContainAnalysis()){
				Main.unsafeConfiguration.add(((Rule)(this)).getRuleName()+" "+signature+" may return: "+returnContain);
				result=true;
				}
				break;
		case 3:if(notAnalysis()){
					switch(not.getMode()){
						case 11: Main.unsafeConfiguration.add(((Rule)(this)).getRuleName()+" "+signature+" can not throw exception: "+(ExceptionContain)(not.getValue()));
								result=true;		
								break;
						case 12: Main.unsafeConfiguration.add(((Rule)(this)).getRuleName()+" "+signature+" can not return: "+(ReturnContain)(not.getValue()));
								result=true;		
								break;
						case 13: Main.unsafeConfiguration.add(((Rule)(this)).getRuleName()+" "+signature+" can not invoke: "+(MethodContain)(not.getValue()));
								result=true;		
								break;
					}
				}
				break;
		case 4:if(this.unsafeMethodCall){
					Set<Unit> callUnits=Main.cfg.getCallersOf(method);
					if(!callUnits.isEmpty()){
						Main.unsafeConfiguration.add(((Rule)(this)).getRuleName()+" "+signature+" was called at: "+callUnits);
						result=true;
					}
			   }
				break;
		case 5:if(methodContainAnalysis()){
				Main.unsafeConfiguration.add(((Rule)this).getRuleName()+" "+signature+" may call "+methodContain.getSignature());
				result=true;
				}
				break;
		case 6:if(bothAnalysis()){
					Not not1=(Not) both.getValue1();
					Not not2=(Not) both.getValue2();
					switch(both.getMode()){
					case "not": Main.unsafeConfiguration.add(((Rule)this).getRuleName()+" "+signature+" both not invoke "+not1.getValue()+" + "+not2.getValue());
								break;
					}
				result=true;
				}
				break;
		}
		if(isHierarchy){//考虑继承，分析子类、implments中的同名函数
			FastHierarchy hierarchy=Scene.v().getOrMakeFastHierarchy();
			String className=Scene.v().signatureToClass(signature);
			SootClass fatherClass=Scene.v().getSootClass(className);
			String subsig=Scene.v().signatureToSubsignature(signature);
			for(SootClass subclass:hierarchy.getSubclassesOf(fatherClass)){
				String subFunction="<"+subclass.getName()+": "+subsig+">";
				MethodConfiguration localMethodConfiguration=new MethodConfiguration(subFunction,getPattern(),Hierarchy);
				localMethodConfiguration.setRuleName(this.getRuleName());
				if(localMethodConfiguration.configurationAnalysis())
					result=true;
			}
			if(fatherClass.isInterface()){
				for(SootClass subclass:hierarchy.getAllImplementersOfInterface(fatherClass)){
					String subFunction="<"+subclass.getName()+": "+subsig+">";
					MethodConfiguration localMethodConfiguration=new MethodConfiguration(subFunction,getPattern(),Hierarchy);
					localMethodConfiguration.setRuleName(this.getRuleName());
					if(localMethodConfiguration.configurationAnalysis())
						result=true;
				}
			}
		}
		return result;
	}
	public boolean exceptionContainAnalysis(){
		for(String localException:exception){
			String s1=localException;
			String s2=exceptionContain.getExceptionValue().toString();
			String tmp[]=s2.split("\\:");
			s2=tmp[0];
			if(s1.equals(s2)){
				return true;
			}
		}
		return false;
	}
	public boolean returnContainAnalysis(){
		List<Unit> retUnits=new ArrayList<Unit>();
		if(!method.hasActiveBody()) return false;
		for(Unit unit:method.getActiveBody().getUnits()){
			if(((Stmt)(unit))instanceof JReturnStmt)
				retUnits.add(unit);
		}
		Dps localDps=new Dps();
		for(Unit retUnit:retUnits){
			localDps.getDps().add(new Dp(new Ep(retUnit),0));
		}
		ConstantPropagation localConstantPropagation=new ConstantPropagation(localDps,(boolean)returnContain.getReturnValue());
		localConstantPropagation.constantPropagationAnalysis(null);
		if(!returnContain.isMust())
			return !localConstantPropagation.getDps().getDps().isEmpty();
		else{
			return localConstantPropagation.getDps().getDps().size()==localDps.getDps().size();
		}
	}
	public boolean notAnalysis(){
		int notMode=not.getMode();
		MethodConfiguration localMC=new MethodConfiguration(signature,not.getValue());
		switch(notMode){
		case 11: return !localMC.exceptionContainAnalysis();
		case 12: return !localMC.returnContainAnalysis();
		case 13: return !localMC.methodContainAnalysis();
		}
		return false;
	}
	public boolean bothAnalysis(){
		String bothMode=both.getMode();
		if(bothMode==null) return false;
		switch(bothMode){
			case "not": Not not1=(Not) both.getValue1();
						Not not2=(Not) both.getValue2();
						MethodConfiguration localMC1=new MethodConfiguration(signature,not1);
						MethodConfiguration localMC2=new MethodConfiguration(signature,not2);
						return localMC1.notAnalysis()&&localMC2.notAnalysis();
		}
		return false;
	}
	public boolean methodContainAnalysis(){
		return methodContainloop(method,methodContain.getMethod(),0);
	}
	private boolean methodContainloop(SootMethod method,SootMethod target,int pathLength){
		pathLength++;
		if(!method.hasActiveBody() || pathLength>Main.CallPathMaxLength) return false;
		for(Unit callee:Main.cfg.getCallsFromWithin(method)){
			SootMethod now=((Stmt)callee).getInvokeExpr().getMethod();
			if(now==target)
				return true;
			else{
				if(methodContainloop(now,target,pathLength))
					return true;
			}
		}
		return false;
	}
	private List<String> getExceptions(){
		List<String> exceptions=new ArrayList<String>();
		if(method!=null && method.hasActiveBody()){
			for(Unit unit:method.getActiveBody().getUnits()){
				if(unit instanceof JThrowStmt && !unit.getUseBoxes().isEmpty()){
					exceptions.add(unit.getUseBoxes().get(0).getValue().getType().toString());
				}
			}
		}
		return exceptions;
	}
}
