package tipsticker;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Pattern;

import soot.FastHierarchy;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;
/**
 * eps is a set of ep.
 * look for Ep.java
 * 
 */
public class Eps extends Main{
	protected List<Ep> eps=new ArrayList<Ep>();
	protected int epsNum=-1;
	
	public Eps(){
	}
	public Eps(String function){
		if(function.equals(ENTRY)){
			Ep entry=new Ep(null);
			entry.setENTRY();
			eps.add(entry);
		}
		else if(function.equals(EXIT)){
			Ep exit=new Ep(null);
			exit.setEXIT();
			eps.add(exit);
		}
		else{
			Pattern pattern=Pattern.compile("^<.*>$");
			if(pattern.matcher(function).matches()){
				eps.addAll(functionInvokeSpecial(function));
			}
			else
				eps.addAll(functionInvokeNormal(function));
		}	
	}
	public Eps(String expr,String New){
		if(New.equals("NewExpr")){
			Iterator<SootClass> classIter = Scene.v().getClasses().iterator();
			while (classIter.hasNext())
			{
				SootClass curClass = classIter.next();
				Iterator<SootMethod> methodIter = curClass.getMethods().iterator();
				while (methodIter.hasNext())
				{
					SootMethod m = methodIter.next();
					if(Main.hasBody(m)){
						for(Unit unit:m.getActiveBody().getUnits()){
							if(unit instanceof JAssignStmt && ((JAssignStmt)unit).getRightOp() instanceof JNewExpr){
								if(((JAssignStmt)unit).getRightOp().toString().equals(expr))
									this.eps.add(new Ep(unit));
							}
						}
					}
				}
			}
		}
			
	}
	Eps(List<Ep> eps){
		this.eps.addAll(eps);
	}
	
	public List<Ep> getEps(){
		return this.eps;
	}
	public void setNum(int v){
		this.epsNum=v;
	}
	public int getNum(){
		return this.epsNum; 
	}
	public void clone(Eps eps){
		this.eps.clear();
		this.eps.addAll(eps.getEps());
		this.epsNum=eps.getNum();
	}
	public boolean contains(Unit u){
		for(Ep ep:this.eps){
			if(ep.getUnit()==u)
				return true;
		}
		return false;
	}
	public Ep getEp(Unit unit){
		for(Ep ep:eps){
			if(ep.getUnit()==unit)
				return ep;
		}
		return null;
	}
	public void remove(Unit u){
		List<Ep> tmp=new ArrayList<Ep>();
		tmp.addAll(this.eps);
		for(Ep ep:tmp){
			if(ep.getUnit()==u)
				this.eps.remove(ep);
		}
	}
	public void add(Unit u){
		this.eps.add(new Ep(u));
	}
	protected List<Ep> functionInvokeSpecial(String signature){
		List<Ep> epList=new ArrayList<Ep>();
		
		Iterator<SootClass> classIter = Scene.v().getClasses().iterator();
		while (classIter.hasNext())
		{
			SootClass curClass = classIter.next();
			Iterator<SootMethod> methodIter = curClass.getMethods().iterator();
			while (methodIter.hasNext())
			{
				SootMethod m = methodIter.next();
				if(Main.hasBody.contains(m)){
					for(Unit unit:m.getActiveBody().getUnits()){
						if(((Stmt)(unit)).containsInvokeExpr()){
							if(((Stmt)(unit)).getInvokeExpr().getMethod().getSignature().equals(signature))
								epList.add(new Ep(unit));
						}
					}
				}				
			}
		}
		
		return epList;
	}
	protected List<Ep> functionInvokeNormal(String function){
		List<Ep> epList=new ArrayList<Ep>();
		String tmp[]=function.split("\\.");
		String className=tmp[0];
		String methodName=null;
		if(tmp.length>=2){
			methodName=tmp[tmp.length-1];
			for(int i=1;i<tmp.length-1;i++)
				className=className+"."+tmp[i];
		}
		else{
			System.out.println("Wrong FunctionInvoke:"+function);
		}
		
		Iterator<SootClass> classIter = Scene.v().getClasses().iterator();
		while (classIter.hasNext())
		{
			SootClass curClass = classIter.next();
			Iterator<SootMethod> methodIter = curClass.getMethods().iterator();
			while (methodIter.hasNext())
			{
				SootMethod m = methodIter.next();
				if(Main.hasBody.contains(m)){
					for(Unit unit:m.getActiveBody().getUnits()){
						if(((Stmt)(unit)).containsInvokeExpr()){
							String localName=((Stmt)(unit)).getInvokeExpr().getMethod().getName();
							String localSignature=((Stmt)(unit)).getInvokeExpr().getMethod().getSignature();
							String localClassName=localSignature.substring(1,localSignature.indexOf(":"));
							if(localName.equals(methodName)&&localClassName.equals(className)){
								epList.add(new Ep(unit));
							}
						}
					}
				}				
			}
		}
		
		return epList;
	}
	protected List<Ep> addSubFunctionInvoke(String function){
		List<Ep> epList=new ArrayList<Ep>();
		FastHierarchy hierarchy=Scene.v().getOrMakeFastHierarchy();
		if(function.charAt(0)=='<'){
			String className=Scene.v().signatureToClass(function);
			SootClass fatherClass=Scene.v().getSootClass(className);
			String subsig=Scene.v().signatureToSubsignature(function);
			for(SootClass subclass:hierarchy.getSubclassesOf(fatherClass)){
				String subFunction="<"+subclass.getName()+": "+subsig+">";
				epList.addAll(functionInvokeSpecial(subFunction));
				epList.addAll(addSubFunctionInvoke(subFunction));
			}
			if(fatherClass.isInterface()){
				for(SootClass subclass:hierarchy.getAllImplementersOfInterface(fatherClass)){
					String subFunction="<"+subclass.getName()+": "+subsig+">";
					epList.addAll(functionInvokeSpecial(subFunction));
					epList.addAll(addSubFunctionInvoke(subFunction));
				}
			}
		}
		else{
			String tmp[]=function.split("\\.");
			String className=tmp[0];
			String methodName=null;
			if(tmp.length>=2){
				methodName=tmp[tmp.length-1];
				for(int i=1;i<tmp.length-1;i++)
					className=className+"."+tmp[i];
			}
			else{
				System.out.println("Wrong FunctionInvoke:"+function);
			}
			SootClass fatherClass=Scene.v().getSootClass(className);
			for(SootClass subclass:hierarchy.getSubclassesOf(fatherClass)){
				String subFunction=subclass.getName()+"."+methodName;
				epList.addAll(functionInvokeNormal(subFunction));
				epList.addAll(addSubFunctionInvoke(subFunction));
			}
			if(fatherClass.isInterface()){
				for(SootClass subclass:hierarchy.getAllImplementersOfInterface(fatherClass)){
					String subFunction=subclass.getName()+"."+methodName;
					epList.addAll(functionInvokeNormal(subFunction));
					epList.addAll(addSubFunctionInvoke(subFunction));
				}
			}
		}
		return epList;
	}
	
	public Eps append(Eps eps){
		this.eps.addAll(eps.getEps());
		return this;
	}
}
