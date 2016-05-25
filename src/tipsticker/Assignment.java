package tipsticker;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.regex.Pattern;

import soot.Body;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.IdentityStmt;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JNewExpr;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JStaticInvokeExpr;
import AssignmentPattern.ConstantValue;
import AssignmentPattern.Match;
import AssignmentPattern.Not;
import AssignmentPattern.OneOf;
import AssignmentPattern.Range;
import AssignmentPattern.StaticValue;
/**
 * @author zxl
 *Assignment is a kind of rule.It can identify if the params of a dps match the pattern
 *for example: Rule r1=Assignment(dps1,3);
 *3 is a intPattern,which means that the critical-param of dp in dps1 is tained if its param  is 3 
 *
 */
public class Assignment extends Rule{
	private Dps dps=new Dps();
	private int intPattern;
	private String stringPattern;
	private Match matchPattern;
	private OneOf oneOfPattern;
	private Range rangePattern;
	private Not notPattern;
	private String staticValue=null;
	private boolean constantValue=false;
	
//every kind of pattern has a special mode-value
//default:-1 intPattern:1 stringPattern:2 matchPattern:3 oneOfPattern:4 rangepattern:5 notPattern:6 StaticValue:7
	private int mode=-1;
	
	Assignment(){
	}
	/**
	 * @param dps: data point set
	 * @param v:	pattern
	 */
	Assignment(Dps dps,Object v){
		this.dps.clone(dps);
		if(v instanceof Integer){
			this.intPattern=(int)v;
			this.mode=1;
		}
		else if(v instanceof String){
			this.stringPattern=(String)v;
			this.mode=2;
		}
		else if(v instanceof Match){
			this.matchPattern=(Match)v;
			this.mode=3;
		}
		else if(v instanceof OneOf){
			this.oneOfPattern=(OneOf)v;
			this.mode=4;
		}
		else if(v instanceof Range){
			this.rangePattern=(Range)v;
			this.mode=5;
		}
		else if(v instanceof Not){
			this.notPattern=(Not)v;
			this.mode=6;
		}
		else if(v instanceof StaticValue){
			this.mode=7;
		}
		else if(v instanceof ConstantValue){
			this.mode=8;
			this.constantValue=true;
		}
	}
	
	public Dps getDps(){
		return this.dps;
	}
	
	public void assignmentAnalysis(IInfoflowCFG cfg,List<Assignment> unsafeAssignment){
		switch(this.mode){
			case 1:
				intAnalysis(cfg,unsafeAssignment);
				break;
			case 2:
				stringAnalysis(cfg,unsafeAssignment);
				break;
			case 3:
				matchAnalysis(cfg,unsafeAssignment);
				break;
			case 4:
				oneOfAnalysis(cfg,unsafeAssignment);
				break;	
			case 5:
				rangeAnalysis(cfg,unsafeAssignment);
				break;
			case 6:
				notAnalysis(cfg,unsafeAssignment);
				break;
			case 7:
				staticValueAnalysis(cfg,unsafeAssignment);
			    break;
			case 8:
				constantValueAnalysis(cfg,unsafeAssignment);
				break;
			default:
			}
		if(unsafeAssignment!=null)
			unsafeAssignment.add(this);
		return;
	}
	
	private boolean intAnalysis(IInfoflowCFG cfg,List<Assignment> assignmentList){
		Dps tmp=new Dps().append(dps);
		ConstantPropagation localConstantPropagation=new ConstantPropagation(tmp,this.intPattern);
		localConstantPropagation.constantPropagationAnalysis(null);
		dps.getDps().clear();
		dps.getDps().addAll(localConstantPropagation.getDps().getDps());
		if(!dps.getDps().isEmpty()){
			return true;
		}
		return false;
	}
	private boolean stringAnalysis(IInfoflowCFG cfg,List<Assignment> assignmentList){
		Dps tmp=new Dps().append(dps);
		ConstantPropagation localConstantPropagation=new ConstantPropagation(tmp,this.stringPattern);
		localConstantPropagation.constantPropagationAnalysis(null);
		
		dps.getDps().clear();
		dps.getDps().addAll(localConstantPropagation.getDps().getDps());
		if(!dps.getDps().isEmpty()){
			return true;
		}
		return false;
	}
	private boolean matchAnalysis(IInfoflowCFG cfg,List<Assignment> assignmentList){
		Pattern pattern=this.matchPattern.getPattern();
		Dps tmp=new Dps().append(dps);
		ConstantPropagation localConstantPropagation=new ConstantPropagation(tmp,pattern);
		localConstantPropagation.constantPropagationAnalysis(null);
		dps.getDps().clear();
		dps.getDps().addAll(localConstantPropagation.getDps().getDps());
		if(!dps.getDps().isEmpty()){
			return true;
		}
		return false;
	}
	private boolean oneOfAnalysis(IInfoflowCFG cfg,List<Assignment> assignmentList){
		int mode=this.oneOfPattern.getMode();
		boolean set=false;
		List<Dp> tmp=new ArrayList<Dp>();
		switch(mode){
			case 1:
				Assignment intAssgn1=new Assignment(dps,this.oneOfPattern.getInt(1));
				Assignment intAssgn2=new Assignment(dps,this.oneOfPattern.getInt(2));	
				if(intAssgn1.intAnalysis(cfg, null)){
					set=true;
					tmp.addAll(intAssgn1.getDps().getDps());
				}
				if(intAssgn2.intAnalysis(cfg, null)){
					set=true;
					tmp.addAll(intAssgn2.getDps().getDps());
				}
				break;
			case 2:
				Assignment stringAssgn1=new Assignment(dps,this.oneOfPattern.getString(1));
				Assignment stringAssgn2=new Assignment(dps,this.oneOfPattern.getString(2));
				if(stringAssgn1.stringAnalysis(cfg, null)){
					set=true;
					tmp.addAll(stringAssgn1.getDps().getDps());
				}
				if(stringAssgn2.stringAnalysis(cfg, null)){
					set=true;
					tmp.addAll(stringAssgn2.getDps().getDps());
				}
				break;
			case 3:
				Assignment matchAssgn1=new Assignment(dps,this.oneOfPattern.getMatch(1));
				Assignment matchAssgn2=new Assignment(dps,this.oneOfPattern.getMatch(2));
				if(matchAssgn1.matchAnalysis(cfg, null)){
					set=true;
					tmp.addAll(matchAssgn1.getDps().getDps());
				}
				if(matchAssgn2.matchAnalysis(cfg, null)){
					set=true;
					tmp.addAll(matchAssgn2.getDps().getDps());
				}
				break;
			case 4:
				Assignment rangeAssgn1=new Assignment(dps,this.oneOfPattern.getRange(1));
				Assignment rangeAssgn2=new Assignment(dps,this.oneOfPattern.getRange(2));
				if(rangeAssgn1.rangeAnalysis(cfg, null)){
					set=true;
					tmp.addAll(rangeAssgn1.getDps().getDps());
				}
				if(rangeAssgn2.rangeAnalysis(cfg, null)){
					set=true;
					tmp.addAll(rangeAssgn1.getDps().getDps());
				}
				break;
			case 5:
				int[] intList=oneOfPattern.getIntList();
				for(int i:intList){
					Assignment local=new Assignment(dps,i);
					if(local.intAnalysis(cfg, null)){
						set=true;
						tmp.addAll(local.getDps().getDps());
					}
				}
				break;
			default:
				
		}
		dps.getDps().clear();
		dps.getDps().addAll(tmp);
		return set;
	}
	private boolean rangeAnalysis(IInfoflowCFG cfg,List<Assignment> assignmentList){
		boolean set=false;
		List<Dp> tmp=new ArrayList<Dp>();
		for(int num=this.rangePattern.getStart();num<=this.rangePattern.getEnd();num++){
			Assignment intAssgn=new Assignment(dps,num);
			if(intAssgn.intAnalysis(cfg, null)){
				set=true;
				tmp.addAll(intAssgn.getDps().getDps());
			}
		}
		dps.getDps().clear();
		dps.getDps().addAll(tmp);
		return set;
	}
	private boolean notAnalysis(IInfoflowCFG cfg,List<Assignment> assignmentList){
		List<Dp> tmp1=new ArrayList<Dp>();
		Dps tmp2=new Dps();
		tmp1.addAll(dps.getDps());		
		Object not=notPattern.getValue();
		Assignment assign=new Assignment(dps,not);
		dps.getDps().clear();
		assign.assignmentAnalysis(cfg, null);
		tmp2=assign.getDps();
		for(Dp dp:tmp1){
			if(!tmp2.contains(dp.getEp().getUnit()))
				dps.getDps().add(dp);
		}
		if(!dps.getDps().isEmpty())
			return true;
		return false;
		
	}
	private boolean staticValueAnalysis(IInfoflowCFG cfg,List<Assignment> assignmentList){
		if(dps.getDps().isEmpty()) return false;
		Unit unit=dps.getDps().get(0).getEp().getUnit();
		ValueBox vb;
		if(!((Stmt)(unit)).containsInvokeExpr()){ 
			dps.getDps().clear();
			return false;
		}
		if(((Stmt)(unit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(unit)).getInvokeExpr().getArgCount())//staticinvoke
			vb=unit.getUseBoxes().get(dps.getArgNum()-1);
		else vb=unit.getUseBoxes().get(dps.getArgNum());
		if(!findStaticDef(unit,vb,new Path())){
			dps.getDps().clear();
			return false;
		}
		ConstantPropagation localConstantPropagation=new ConstantPropagation(dps,staticValue);
		boolean set=false;
		
		if(localConstantPropagation.mustConstantPropagation()){
			if(dps.getDps().size()==localConstantPropagation.getDps().getDps().size())
				set=true;
		}
		if(!set) dps.getDps().clear();
		return set;
	}
	private boolean constantValueAnalysis(IInfoflowCFG cfg,List<Assignment> assignmnetList){
		if(dps.getDps().isEmpty()) return false;
		Unit unit=dps.getDps().get(0).getEp().getUnit();
		if(!((Stmt)(unit)).containsInvokeExpr()){ 
			dps.getDps().clear();
			return false;
		}
		ConstantPropagation localConstantPropagation=new ConstantPropagation(dps,new ConstantValue());
		localConstantPropagation.mustConstantPropagation();
		dps.getDps().clear();
		dps.getDps().addAll(localConstantPropagation.getDps().getDps());
		return !dps.getDps().isEmpty();
	}
	private boolean implicitIntentAnalysis(IInfoflowCFG cfg,List<Assignment> assignmentList){
		if(dps.getDps().isEmpty()) return false;
		
		
		return true;
	}   
	private boolean isExplicitIntent(Unit unit,ValueBox vb){
		List<Unit> defUnits=findDefUnit(unit,vb);

		for(Unit def:defUnits){
			//$r=new android.content.Intent
			boolean set=false;
			if(def instanceof JAssignStmt && ((JAssignStmt) def).getRightOp() instanceof JNewExpr){
				List<Unit> directUse=new ArrayList<Unit>();
				findUseUnit(def,def.getDefBoxes().get(0),directUse);
				for(Unit use:directUse){
					if(((Stmt)use).containsInvokeExpr()){
						String signature=((Stmt)use).getInvokeExpr().getMethod().getSignature();
							if(signature.equals("<android.content.Intent: android.content.Intent setClass(android.content.Context,java.lang.Class)>")
								|| signature.equals("<android.content.Intent: void <init>(android.content.Context,java.lang.Class)>")
								|| signature.equals("<android.content.Intent: void <init>(java.lang.String,android.net.Uri,android.content.Context,java.lang.Class)>")
								)
								set=true;
							else if(signature.equals("<android.content.Intent: void <init>(android.content.Intent)>"))
								set=isExplicitIntent(use,use.getUseBoxes().get(1));
							else{
								SootMethod m=((Stmt)use).getInvokeExpr().getMethod();
								if(Main.hasBody(m)){
									int ArgNum=-1;
									for(int i=0;i<use.getUseBoxes().size();i++){
										if(use.getUseBoxes().get(i).getValue().toString().equals(vb.getValue().toString()))
											ArgNum=i;
									}
									if(((Stmt)use).getInvokeExpr() instanceof JStaticInvokeExpr) ArgNum++;
									for(Unit sub:m.getActiveBody().getUnits()){
										if(ArgNum==0 && sub instanceof JAssignStmt && ((JAssignStmt)sub).getRightOp() instanceof ThisRef){
											set=isExplicitIntent(sub,sub.getDefBoxes().get(0));
										}
										else if(ArgNum>0 && sub instanceof JAssignStmt){
											Local subLocal=null;
											Body subBody=m.getActiveBody();
											if(ArgNum!=0){
												subLocal=subBody.getParameterLocal(ArgNum-1);
											}
											else{
												subLocal=subBody.getThisLocal();
											}
											Unit defUnit=null;
											for(Unit subUnit:subBody.getUnits()){
												if(!subUnit.getDefBoxes().isEmpty()){
													Value tmp=subUnit.getDefBoxes().get(0).getValue();
													if(tmp==((Value)(subLocal))){
														defUnit=subUnit;
														break;
													}
												}
											}
											if(defUnit==null)
											continue;
											set=isExplicitIntent(defUnit,defUnit.getDefBoxes().get(0));
										}
									}
								}
							}
					}
				}
			}
			//$r=virtualInvoke $r7.<my local method>()
			else if(((Stmt)def).containsInvokeExpr()){
				List<Unit> retUnit=new ArrayList<Unit>();
				if(!Main.hasBody(Main.cfg.getMethodOf(def)))
					continue;
				for(Unit u:Main.cfg.getMethodOf(def).getActiveBody().getUnits()){
					if(u instanceof JReturnStmt)
						retUnit.add(u);
				}
				boolean flag=true;
				for(Unit ret:retUnit){
					if(!isExplicitIntent(ret,ret.getUseBoxes().get(0)))
						flag=false;
				}
				if(flag) set=true;
			}
			else if(def instanceof JAssignStmt &&((JAssignStmt)def).getRightOp() instanceof ThisRef){
				
			}
		}
		
		return true;
	}
	/**
	 * 判断vb是否可以用来作为一个staticValue，这里只是判断是否为constant
	 * 该函数可以用contant类简化
	 * @param vb
	 * @return
	 */
	private boolean isStaticValue(ValueBox vb){
		if(staticValue==null){
			String local=vb.getValue().toString();
			Pattern pattern1=Pattern.compile("^[$].*");
			Pattern pattern2=Pattern.compile("^new .*");
			Pattern pattern3=Pattern.compile("^@this:.*");
			Pattern pattern4=Pattern.compile("^@parameter.*");
			if(!pattern1.matcher(local).matches()&&!pattern2.matcher(local).matches()&&!pattern3.matcher(local).matches()&&!pattern4.matcher(local).matches()){
				Pattern quot=Pattern.compile("^\".*\"$");
				if(quot.matcher(local).matches()){
					local=local.substring(1, local.length()-1);
				}
				staticValue=local;
				return true;
			}
		}
		else{
			return staticValue.equals(vb.getValue().toString());
		}
		return false;
	}
	/**
	 * 采用迭代的方法向前遍历，直到找到一个constant
	 * @param unit 当前遍历的unit
	 * @param vb 当前遍历的vb
	 * @param path 用来记录遍历时经过的函数调用
	 * @return
	 */
	private boolean findStaticDef(Unit unit,ValueBox vb,Path path){
		if(isStaticValue(vb)){
			return true;
		}
		List<Unit> tmpDef=findDefUnit(unit,vb);
		for(Unit tmp:tmpDef){
			//遇到一个函数调用，如果该函数有body，那么进入该body，并以它的ret语句为起点继续迭代遍历
			if(((Stmt)(tmp)).containsInvokeExpr()){
				SootMethod method=((Stmt)(tmp)).getInvokeExpr().getMethod();
				List<Unit> retUnits=new ArrayList<Unit>();
				if(Main.hasBody(method)){
					path.getPath().add(tmp);
					for(Unit u:method.getActiveBody().getUnits()){
						if((Stmt)u instanceof JReturnStmt)
							retUnits.add(u);
					}
					for(Unit retUnit:retUnits){
						if(retUnit.getUseBoxes().isEmpty())
							return false;
						if(!findStaticDef(retUnit,retUnit.getUseBoxes().get(0),new Path(path)))
							return false;
					}
				return true;
				}
				else{//如果没有body，以this位置的valuebox为起点继续迭代遍历
					if(((Stmt)(tmp)).getInvokeExpr().getUseBoxes().size()==((Stmt)(tmp)).getInvokeExpr().getArgCount())//staticinvoke
						return false;//staticinvoke没有this位置的valuebox
					if(((Stmt)tmp).getInvokeExpr().getArgCount()!=0)
						return false;//有参数的no-body函数处理比较麻烦，目前按false处理
					return findStaticDef(tmp,tmp.getUseBoxes().get(0),path);
				}
			}
			//遇到filed，确认该filed的值是constant
			else if(((Stmt)(tmp)).containsFieldRef()){
				for(Unit field:Main.defField.get(((Stmt)(tmp)).getFieldRef().getField())){
					if(field instanceof JAssignStmt &&!isStaticValue(((JAssignStmt)field).getRightOpBox())){
						return false;
					}
				}
				return true;
			}
			//其他情况下，只处理等式右侧只有一个valuebox的情况，包含$i=@this:.....和$i=@param:....这2中情况
			else if(tmp.getUseBoxes().size()==1){
				if(isStaticValue(tmp.getUseBoxes().get(0))){
					
					return true;
				}
				//确认是否为this，是的话，就以调用该函数的unit为起点
				else if(getThisLocal(Main.cfg.getMethodOf(unit).getActiveBody())!=null) 
					if(Main.cfg.getMethodOf(unit).getActiveBody().getThisLocal().getName()==tmp.getDefBoxes().get(0).getValue().toString()){
					if(!path.getPath().isEmpty()){//path里记录的是之前遇到的函数调用语句
						Unit callUnit=path.getPath().get(path.getPath().size()-1);
						if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(callUnit)).getInvokeExpr().getArgCount())//staticinvoke
							return false;
						Path tmpPath=new Path(path);
						tmpPath.getPath().remove(path.getPath().size()-1);
						if(findStaticDef(callUnit,callUnit.getUseBoxes().get(0),tmpPath))
							return true;
						return false;
					}//若path为空，则所有的caller-unit都是可能的
					for(Unit callUnit:Main.cfg.getCallersOf(Main.cfg.getMethodOf(unit))){
						if(((Stmt)(unit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(unit)).getInvokeExpr().getArgCount())//staticinvoke
							continue;
						if(!findStaticDef(callUnit,callUnit.getUseBoxes().get(0),new Path(path)))
							return false;
					}
					return true;
				}
				//确认是否为param，是的话，就以调用该函数的unit为起点
				else{
					for(int i=0;i<Main.cfg.getMethodOf(unit).getParameterCount();i++){
						if(vb.getValue().toString()==Main.cfg.getMethodOf(unit).getActiveBody().getParameterLocal(i).getName()){
							if(!path.getPath().isEmpty()){
								Unit callUnit=path.getPath().get(path.getPath().size()-1);
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i++;
								Path tmpPath=new Path(path);
								tmpPath.getPath().remove(path.getPath().size()-1);
								if(!findStaticDef(callUnit,callUnit.getUseBoxes().get(i),tmpPath))
									return false;
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i--;//把前面加的减掉
								return true;
							}
							for(Unit callUnit:Main.cfg.getCallersOf(Main.cfg.getMethodOf(unit))){
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i++;
								if(!findStaticDef(callUnit,callUnit.getUseBoxes().get(i),new Path(path)))
									return false;
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i--;
							}
							return true;
						}
					}
				}
			}
		}
		return false;
	}
	private boolean findUseUnit(Unit unit, ValueBox vb,List<Unit> useUnit){
		if(!Main.hasBody(Main.cfg.getMethodOf(unit))) return false;
		Body b=Main.cfg.getMethodOf(unit).getActiveBody();
		return Propagation.findUseUnit(Main.cfg, b, vb, useUnit);
	}
	private  List<Unit> findDefUnit(Unit unit,ValueBox vb){
		List<Unit> tmpDef=new ArrayList<Unit>();
		if(unit instanceof JAssignStmt && unit.getDefBoxes().get(0)==vb){
			tmpDef.add(unit);
		}
		else
			ConstantPropagation.findDefUnit(unit,vb,new ArrayList<Unit>(),tmpDef);
		return tmpDef;
	}
	/**
	 * this-local is a local defined by unit " $r0=@this:**** "
	 * it stands for this("a") in a method-call unit " a.b() " 
	 * a body only can has one this-local at most.
	 * @param Body b
	 * @return Local this
	 */
	private Local getThisLocal(Body b){
		Iterator<Unit> unitsIt = b.getUnits().iterator();
        while (unitsIt.hasNext())
        {
            Unit s = unitsIt.next();
            if (s instanceof IdentityStmt &&
                ((IdentityStmt)s).getRightOp() instanceof ThisRef)
                return (Local)(((IdentityStmt)s).getLeftOp());
        }
        return null;
	}
	
	public boolean isEmpty(){
		return this.dps.getDps().isEmpty();
	}
	public void clear(){
		this.dps.getDps().clear();
	}
	
	
	
	
}
