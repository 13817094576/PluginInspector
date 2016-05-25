package tipsticker;

import java.util.ArrayList;
import java.util.List;

import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
import soot.jimple.FieldRef;
import soot.jimple.InvokeExpr;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JStaticInvokeExpr;

public class DataExecution {
	private IInfoflowCFG cfg=Main.cfg;
	private List<Value> propaData=new ArrayList<Value>();
	private List<Dp> path=new ArrayList<Dp>();
	private List<Unit> callPath=new ArrayList<Unit>();
	private List<Unit> propagationPath=new ArrayList<Unit>();
	List<Unit> badUnit=new ArrayList<Unit>();
	private Dps end=new Dps();
	private Unit now;
	
	private int liveStatus=1;
	private int living=1;
	private int dead=2;
	private int reachEnd=3;
	DataExecution(Dp dp,Value v,Unit n,Dps e){
		path.add(dp);
		propagationPath.add(n);
		propaData.add(v);
		now=n;
		end.clone(e);
	}
	DataExecution(DataExecution de){
		path.addAll(de.getPath());
		callPath.addAll(de.getCallPath());
		propaData.addAll(de.getPropaData());
		liveStatus=de.getStatus();
		now=de.getNowUnit();
		end.clone(de.getEndDps());
		badUnit.addAll(de.getBadUnit());
		propagationPath.addAll(de.getPropagationPath());
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
	public List<Unit> getBadUnit(){
		return this.badUnit;
	}
	public List<Unit> getPropagationPath(){
		return this.propagationPath;
	}
	public List<Unit> getCallPath(){
		return this.callPath;
	}
	public List<Value> getPropaData(){
		return this.propaData;
	}
	public Dps getEndDps(){
		return this.end;
	}
	public int getStatus(){
		return this.liveStatus;
	}
	public void remove(Value v){
		propaData.remove(v);
		if(propaData.isEmpty())
			liveStatus=dead;
	}
	public void remove(Dp dp){
		path.remove(dp);
	}
	public void kill(){
		liveStatus=dead;
	}
	public boolean isliving(){
		return liveStatus==living;
	}
	public boolean isdead(){
		return liveStatus==dead;
	}
	public boolean isreachEnd(){
		return liveStatus==reachEnd;
	}
	public List<DataExecution> breed(){
		List<DataExecution> son=new ArrayList<DataExecution>();
		if(liveStatus==living && callPath.size()<=Main.CallPathMaxLength){
			List<Unit> units=new ArrayList<Unit>();
			badSuccs.clear();
			units.addAll(getSuccs(now,new ArrayList<Unit>()));
			//	units.add(now);
			for(Unit succs:units){
				//if(badUnit.contains(succs)) continue;
				DataExecution sub=new DataExecution(this);
				sub.now=succs;
				sub.getPropagationPath().add(succs);
				if(unitUseValue(succs)!=null){
					int argIndex=getArgIndex(succs,unitUseValue(succs));
					Dp succsDp=new Dp(succs,argIndex);
					if(loopDp(succsDp)){
						continue;
					}
					sub.getPath().add(succsDp);
					if(end.contains(succsDp)){
						sub.liveStatus=reachEnd;
						son.add(sub);
						continue;
					}
					if(succs instanceof ReturnStmt){
						List<Unit> callUnits=getCallUnit(succs);
						for(Unit callUnit:callUnits){
							DataExecution callDE=new DataExecution(sub);
							callDE.getPropagationPath().add(callUnit);
							callDE.getPropaData().clear();
							callDE.setNowUnit(callUnit);
							if(callUnit instanceof JAssignStmt || callUnit instanceof JIdentityStmt){
								callDE.getPath().add(new Dp(callUnit,-1));
								callDE.getPropaData().add(callUnit.getDefBoxes().get(0).getValue());
							}
							else if(((Stmt)callUnit).containsInvokeExpr() && !(((Stmt)callUnit).getInvokeExpr() instanceof JStaticInvokeExpr)){
								callDE.getPath().add(new Dp(callUnit,0));
								callDE.getPropaData().add(callUnit.getUseBoxes().get(0).getValue());
							}
							else{
								callDE.getPath().add(new Dp(callUnit,-2));
								callDE.kill();
							}
							son.add(callDE);
						}
					}
					else if(((Stmt)succs).containsInvokeExpr()){
						InvokeExpr invoke=((Stmt)succs).getInvokeExpr();
						SootMethod m=invoke.getMethod();
						if(Main.hasBody(m)){
							Dp invokeDp=getInerInvokeDp(succs,argIndex);
							sub.getPath().add(invokeDp);
							if(invokeDp==null){
								sub.kill();
								son.add(sub);
							}
							else{
								DataExecution subBrother=new DataExecution(this);
								sub.getCallPath().add(succs);
								sub.getPropaData().clear();
								sub.setNowUnit(invokeDp.getEp().getUnit());
								sub.getPropaData().add(invokeDp.getEp().getUnit().getDefBoxes().get(0).getValue());
								son.add(sub);
								subBrother.setNowUnit(succs);
								subBrother.getPropagationPath().add(succs);
								son.add(subBrother);
							}
						}
						else{
							if(!(invoke instanceof JStaticInvokeExpr)){
								Dp invokeDp=new Dp(succs,0);
								Value v=succs.getUseBoxes().get(0).getValue();
								//这里加入类型检查只是临时的解决方案，问题出于getSuccs()无限循环
								if(!sub.getPropaData().contains(v) && v.getType().equals(sub.getPropaData().get(0).getType()))
									sub.getPropaData().add(v);
								//sub.getPath().add(invokeDp);
								sub.setNowUnit(succs);
								son.add(sub);
							}
						}
					}
					else if(succs instanceof JAssignStmt 
							&& ((JAssignStmt)succs).getLeftOp() instanceof FieldRef 
							&& Main.useField.containsKey(((Stmt)(succs)).getFieldRef().getField())){
						Dp field=new Dp(succs,-1);
						sub.getPath().add(field);
						
						for(Unit fieldUse:Main.useField.get(((Stmt)(succs)).getFieldRef().getField())){
							DataExecution fieldDE=new DataExecution(sub);
							if(cfg.getMethodOf(succs)!=cfg.getMethodOf(fieldUse))
								fieldDE.getPropaData().clear();
							Value v=fieldUse.getDefBoxes().get(0).getValue();
							if(!fieldDE.getPropaData().contains(v))
								fieldDE.getPropaData().add(v);
							fieldDE.setNowUnit(fieldUse);
							fieldDE.getPath().add(new Dp(fieldUse,-1));
							fieldDE.getPropagationPath().add(fieldUse);
							son.add(fieldDE);
						}
					}
					else if(succs instanceof JAssignStmt && ((JAssignStmt)succs).getLeftOp() instanceof ArrayRef){
						Dp array=new Dp(succs,-1);
						sub.getPath().add(array);
						for(Unit arrayUse:Main.useArray.get(((ArrayRef)((JAssignStmt)succs).getLeftOp()).getBase())){
							DataExecution arrayDE=new DataExecution(sub);
							if(cfg.getMethodOf(succs)!=cfg.getMethodOf(arrayUse))
								arrayDE.getPropaData().clear();
							Value v=arrayUse.getDefBoxes().get(0).getValue();
							if(!arrayDE.getPropaData().contains(v))
								arrayDE.getPropaData().add(v);
							arrayDE.setNowUnit(arrayUse);
							arrayDE.getPath().add(new Dp(arrayUse,-1));
							arrayDE.getPropagationPath().add(arrayUse);
							son.add(arrayDE);
						}
					}
				}
				else if(unitDefValue(succs)!=null){
					sub.getPropaData().remove(unitDefValue(succs));
					sub.setNowUnit(succs);
					son.add(sub);
				}
			}
			if(son.isEmpty()) badUnit.addAll(badUnits(now));
		}
		
		return son;
	}
	List<Unit> goodSuccs=new ArrayList<Unit>();
	List<Unit> badSuccs=new ArrayList<Unit>();
	private List<Unit> getSuccs(Unit s,List<Unit> path){
		List<Unit> succsUnit=new ArrayList<Unit>();
		SootMethod m=cfg.getMethodOf(s);
		//path.size()>100只是临时解决方案
		if(path.contains(s)||badSuccs.contains(s)||path.size()>100){ 
			
			return succsUnit;
		}
		path.add(s);
		
		//<battery.nuko.nuko.widget.BatteryNukoWidget$WidgetService: int onStartCommand(android.content.Intent,int,int)>
		//if(path.size()==4000)
		//	System.out.println(path.size());
			
		for(Unit succs:cfg.getSuccsOf(s)){
			if(unitUseValue(succs)!=null || unitDefValue(succs)!=null){
				if(!succsUnit.contains(succs))
					succsUnit.add(succs);
			}
			else{
				List<Unit> localPath=new ArrayList<Unit>();
				localPath.addAll(path);
				succsUnit.addAll(getSuccs(succs,localPath));
			}
		}
		if(succsUnit.isEmpty()) badSuccs.add(s);
		return succsUnit;
	}
	private List<Unit> badUnits(Unit s){
		List<Unit> badunit=new ArrayList<Unit>();
		if(cfg.getPredsOf(s).size()==1){
			badunit.addAll(cfg.getPredsOf(s));
			badunit.addAll(badUnits(cfg.getPredsOf(s).get(0)));
		}
		return badunit;
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
}
