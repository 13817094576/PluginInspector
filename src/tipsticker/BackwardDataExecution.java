package tipsticker;

import java.util.ArrayList;
import java.util.List;

import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.InvokeExpr;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JStaticInvokeExpr;
import soot.jimple.toolkits.pointer.PASideEffectTester;

public class BackwardDataExecution {
	private IInfoflowCFG cfg=Main.cfg;
	private List<Value> propaData=new ArrayList<Value>();
	private List<Dp> path=new ArrayList<Dp>();
	private List<Unit> callPath=new ArrayList<Unit>();
	private Dps start=new Dps();
	private Unit now;
	
	private String liveStatus="living";
	
	BackwardDataExecution(Dp dp,Value v,Unit n,Dps e){
		path.add(dp);
		propaData.add(v);
		now=n;
		start.clone(e);
	}
	BackwardDataExecution(BackwardDataExecution de){
		path.addAll(de.getPath());
		callPath.addAll(de.getCallPath());
		propaData.addAll(de.getPropaData());
		liveStatus=de.getStatus();
		now=de.getNowUnit();
		start.clone(de.getStartDps());
	}
	public Unit getNowUnit(){
		return now;
	}
	public void setNowUnit(Unit n){
		now=n;
	}
	public List<Dp> getPath(){
		return this.path;
	}
	public List<Unit> getCallPath(){
		return this.callPath;
	}
	public List<Value> getPropaData(){
		return this.propaData;
	}
	public Dps getStartDps(){
		return this.start;
	}
	public String getStatus(){
		return this.liveStatus;
	}
	public void remove(Value v){
		propaData.remove(v);
		if(propaData.isEmpty())
			liveStatus="dead";
	}
	public void remove(Dp dp){
		path.remove(dp);
	}
	public void kill(){
		liveStatus="dead";
	}
	public boolean isliving(){
		return liveStatus=="living";
	}
	public boolean isdead(){
		return liveStatus=="dead";
	}
	public boolean isreachEnd(){
		return liveStatus=="reachEnd";
	}
	
	public List<BackwardDataExecution> findPath(){
		List<BackwardDataExecution> parent=new ArrayList<BackwardDataExecution>();
		if(start.contains(now)){
			path.add(new Dp(now,getArgIndex(now,unitUseValue(now))));
			liveStatus="reachEnd";
			parent.add(this);
			return parent;
		}
		
		if(liveStatus=="living")
		for(Unit pre:findPreDefAndUse(now)){
			Value def=unitDefValue(now);
			Value use=unitUseValue(now);
			if(def!=null){
				path.add(new Dp(pre,-1));
				if(start.contains(pre)){
					liveStatus="reachEnd";
					parent.add(this);
					return parent;
				}
				else if(((Stmt)pre).containsInvokeExpr()){
					InvokeExpr exp=((Stmt)pre).getInvokeExpr();
					SootMethod m=((Stmt)pre).getInvokeExpr().getMethod();
					if(!Main.hasBody(m)){
						BackwardDataExecution sup=new BackwardDataExecution(this);
						sup.getPropaData().remove(def);
						for(Value v:exp.getArgs())
								sup.getPropaData().add(v);
						sup.setNowUnit(pre);
						if(m.getParameterCount()!=0 && exp instanceof JStaticInvokeExpr){
							parent.add(sup);
						}
						else if(m.getParameterCount()!=0 && !(exp instanceof JStaticInvokeExpr)){
							sup.getPropaData().add(pre.getUseBoxes().get(0).getValue());
							parent.add(sup);
						}
						else if(m.getParameterCount()==0 && !(exp instanceof JStaticInvokeExpr)){
							sup.getPropaData().add(pre.getUseBoxes().get(0).getValue());
							parent.add(sup);
						}
					}
					else{
						for(Unit ret:getRetUnit(m)){
							BackwardDataExecution sup=new BackwardDataExecution(this);
							sup.getPropaData().clear();
							sup.getPropaData().add(ret.getUseBoxes().get(0).getValue());
							sup.getPath().add(new Dp(ret,0));
							sup.setNowUnit(ret);
							parent.add(sup);
						}
					}
				}
				else if(((Stmt)pre).containsFieldRef()){
					for(Unit defField:Main.defField.get(((Stmt)pre).getFieldRef().getField())){
						BackwardDataExecution sup=new BackwardDataExecution(this);
						sup.getPropaData().clear();
						sup.getPropaData().add(defField.getUseBoxes().get(0).getValue());
						sup.getPath().add(new Dp(defField,-1));
						sup.setNowUnit(defField);
						parent.add(sup);
					}
				}
				else if(pre instanceof JIdentityStmt){
					
				}
			}
		}
		
		return parent;
	}
	private List<Unit> findPreDefAndUse(Unit s){
		List<Unit> preDefAndUse=new ArrayList<Unit>();
		for(Unit pre:Main.cfg.getPredsOf(s)){
			if(unitUseValue(pre)!=null || unitDefValue(pre)!=null)
				preDefAndUse.add(pre);
			else
				preDefAndUse.addAll(findPreDefAndUse(pre));
			
		}
		return preDefAndUse;
	}
	
	private Value unitUseValue(Unit s){
		for(ValueBox vb:s.getUseBoxes()){
			if(propaData.contains(vb.getValue()))
				return vb.getValue();
		}
		return null;
	}
	private int getArgIndex(Unit s,Value v){
		int i;
		for(i=0;i<s.getUseBoxes().size();i++){
			if(s.getUseBoxes().get(i).getValue()==v)
				break;
		}
		if(((Stmt)s).containsInvokeExpr() && ((Stmt)s).getInvokeExpr() instanceof JStaticInvokeExpr)
			i++;
		return i;
	}
	private Value unitDefValue(Unit s){
		if(s instanceof JAssignStmt || s instanceof JIdentityStmt)
			if(propaData.contains(s.getDefBoxes().get(0).getValue()))
				return s.getDefBoxes().get(0).getValue();
		return null;
	}
	private List<Unit> getCallUnit(Unit s){
		List<Unit> callUnit=new ArrayList<Unit>();
		if(callPath.isEmpty())
			callUnit.addAll(cfg.getCallersOf(cfg.getMethodOf(s)));
		else{
			int lastIndex=callPath.size()-1;
			callUnit.add(callPath.get(lastIndex));
			callPath.remove(lastIndex);
		}
		return callUnit;
	}
	private Dp getInerInvokeDp(Unit s,int argNum){
		SootMethod m=((Stmt)s).getInvokeExpr().getMethod();
		if(!Main.hasBody(m)) return null;
		if(((Stmt)s).getInvokeExpr() instanceof JStaticInvokeExpr && argNum==0) return null;
		if(argNum==0){
			for(Unit unit:m.getActiveBody().getUnits()){
				if(unit instanceof JIdentityStmt && ((JIdentityStmt) unit).getRightOp() instanceof ThisRef){
					return new Dp(unit,-1);
				}
			}
		}
		else{
			Value v=m.getActiveBody().getParameterLocal(argNum-1);
			for(Unit unit:m.getActiveBody().getUnits()){
				if(unit instanceof JIdentityStmt && ((JIdentityStmt) unit).getLeftOp()==v)
					return new Dp(unit,-1);
			}
		}
		return null;
	}
	
	private boolean loopDp(Dp dp){
		for(Dp local:path){
			if(local.getEp().getUnit()==dp.getEp().getUnit() && local.getArgNum()==dp.getArgNum())
				return true;
		}
		return false;
	}
	private List<Unit> getRetUnit(SootMethod m){
		List<Unit> retUnit=new ArrayList<Unit>();
		for(Unit ret:m.getActiveBody().getUnits()){
			if((Stmt)ret instanceof JReturnStmt)
				retUnit.add(ret);
		}
		return retUnit;
	}
}
