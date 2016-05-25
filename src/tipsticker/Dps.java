package tipsticker;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;

import soot.Body;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;

public class Dps {
	protected List<Dp> dps=new ArrayList<Dp>();
	//the argNum of param,0 is this, 1 is the fist param, 2 is the second param....
	//for example: a.b(c,d); a is this,its argNum is 0,;c is the fist parm, its argNum is 1
	protected int dpsNum=-1;
	
	public Dps(){
	}
	public Dps(String function,int argNum){
		Eps tmpeps=Main.FunctionInvoke(function);
		if((tmpeps==null)||(argNum<-1)){
			System.out.println("Wrong Arg:"+function+"\t"+argNum);
		}
		else{
			for(Ep tmpep:tmpeps.getEps()){
				if(((Stmt)(tmpep.getUnit())).getInvokeExpr().getMethod().getParameterCount()<argNum)
					continue;
				Dp dp=new Dp(tmpep,argNum);
				dps.add(dp);
			}
		}
	}
	
	public Dps(String field){
		String tmp[]=field.split("\\.");
		String className=tmp[0];
		String fieldName=null;
		if(tmp.length>=2){
			fieldName=tmp[tmp.length-1];
			for(int i=1;i<tmp.length-1;i++)
				className=className+"."+tmp[i];
		}
		else{
			System.out.println("Wrong Field:"+field);
		}
		if(tmp.length>=2)
		for (Iterator<MethodOrMethodContext> iter = Scene.v().getReachableMethods().listener(); iter.hasNext();) {
			SootMethod m = iter.next().method();
			if (m.isConcrete()) {
				Body b = m.retrieveActiveBody();				
				for (Unit unit: b.getUnits()) {
					if(unit instanceof Stmt){
						if(!((Stmt)(unit)).containsFieldRef()||unit.getDefBoxes().isEmpty()||((Stmt)(unit)).getFieldRefBox()!=unit.getDefBoxes().get(0)) continue;
						String getName=((Stmt)(unit)).getFieldRef().getField().getName();
						String signature=((Stmt)(unit)).getFieldRef().getField().getSignature();
						String[] tmpary=signature.split(":");
						String tmpClass=tmpary[0].substring(1);
						if(getName.equals(fieldName)){
							if(tmpClass.equals(className)){
							Ep ep=new Ep(unit);
							dps.add(new Dp(ep,-1));
							}
						}
					}
				}
			}	
		}
	}
	public Dps(String expr,String New){
		if(New.equals("NewExpr")){
			for (Iterator<MethodOrMethodContext> iter = Scene.v().getReachableMethods().listener(); iter.hasNext();) {
				SootMethod m = iter.next().method();
				if(Main.hasBody(m)){
					for(Unit unit:m.getActiveBody().getUnits()){
						if(unit instanceof JAssignStmt && ((JAssignStmt)unit).getRightOp() instanceof JNewExpr){
							if(((JAssignStmt)unit).getRightOp().toString().equals(expr))
								this.dps.add(new Dp(new Ep(unit),-1));
						}
					}
				}
			}
		}
			
	}
	Dps(List<Dp> dps){
		this.dps.addAll(dps);
	}
	
	public List<Dp> getDps(){
		return this.dps;
	}
	public void setNum(int v){
		this.dpsNum=v;
	}
	public int getNum(){
		return this.dpsNum; 
	}
	public int getArgNum(){
		if(dps.isEmpty())
			return -1;
		else
			return dps.get(0).getArgNum();
	}
	public boolean contains(Unit u){
		for(Dp dp:this.dps){
			if(dp.getEp().getUnit()==u)
				return true;
		}
		return false;
	}
	public boolean contains(Dp dp){
		for(Dp local:dps){
			if(local.getEp().getUnit()==dp.getEp().getUnit()&&local.getArgNum()==dp.getArgNum())
				return true;
		}
		return false;
	}
	public void remove(Unit u){
		List<Dp> tmp=new ArrayList<Dp>();
		tmp.addAll(dps);
		dps.clear();
		for(Dp dp:tmp){
			if(dp.getEp().getUnit()!=u)
				dps.add(dp);
		}
	}
	public void clone(Dps dps){
		this.dps.clear();
		this.dps.addAll(dps.getDps());
		this.dpsNum=dps.getNum();
	}
	public Dps append(Dps dps){
		this.dps.addAll(dps.getDps());
		return this;
	}
	
}
