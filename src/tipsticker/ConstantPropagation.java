package tipsticker;

import java.util.ArrayList;
import java.util.List;
import java.util.regex.Pattern;

import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
import soot.jimple.Constant;
import soot.jimple.IdentityStmt;
import soot.jimple.Stmt;
import soot.jimple.ThisRef;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JReturnStmt;
import AssignmentPattern.ConstantValue;
public class ConstantPropagation extends Rule{
	private Dps dps=new Dps();
	
	
	private int intValue;
	private String stringValue;
	private boolean booleanValue;
	private Pattern matchValue;
	private boolean constantValue=false;
	
	private static String PROP_MAY="prop_may";
	private static String PROP_MAYNOT="prop_maynot";
	
	private String mode;
	private int pattern=-1;
	
	ConstantPropagation(Dps dps,Object v){
		this.dps.clone(dps);
	//	this.mode=mode;
		if(v instanceof Integer){
			intValue=(Integer)(v);
			pattern=1;
		}
		if(v instanceof String){
			stringValue=(String)(v);
			pattern=2;
		}
		if(v instanceof Boolean){
			booleanValue=(Boolean)(v);
			pattern=3;
		}
		if(v instanceof Pattern){
			matchValue=(Pattern)(v);
			pattern=4;
		}
		if(v instanceof ConstantValue){
			constantValue=true;
			pattern=5;
		}
	}
	
	
	public Object getValue(){
		switch(pattern){
		case 1:return intValue;
		case 2:return stringValue;
		case 3:return booleanValue;
		case 4:return matchValue;
		case 5:return constantValue;
		}
		return null;
	}
	public Dps getDps(){
		return dps;
	}
	
	/**
	 * 默认采用mayconstantdef
	 * 要采用must模式的话，使用下面的mustconstantPropagation（）
	 * @param unsafeConstantPropagation
	 */
	public void constantPropagationAnalysis(List<ConstantPropagation> unsafeConstantPropagation){
		Dps tmp=new Dps();
		tmp.clone(dps);
		dps.getDps().clear();
		for(Dp dp:tmp.getDps()){
			int i=dp.getArgNum();
			Unit unit=dp.getEp().getUnit();
			if(((Stmt)(unit)).containsInvokeExpr()&&((Stmt)(unit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(unit)).getInvokeExpr().getArgCount())//staticinvoke
				i--;
			ValueBox vb=unit.getUseBoxes().get(i);
			if(mayConstantDef(unit,vb,new Path(),new ArrayList<ValueBox>()))//defalut is may
				dps.getDps().add(dp);
		}
		if(unsafeConstantPropagation==null)
			return;
		if(!this.dps.getDps().isEmpty())
			unsafeConstantPropagation.add(this);
	}
	
	public boolean mustConstantPropagation(){
		Dps tmp=new Dps();
		tmp.clone(dps);
		dps.getDps().clear();
		for(Dp dp:tmp.getDps()){
			int i=dp.getArgNum();
			Unit unit=dp.getEp().getUnit();
			if(((Stmt)(unit)).containsInvokeExpr()&&((Stmt)(unit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(unit)).getInvokeExpr().getArgCount())//staticinvoke
				i--;
			ValueBox vb=unit.getUseBoxes().get(i);
			if(mustConstantDef(unit,vb,new Path(),new ArrayList<ValueBox>()))//must mode
				dps.getDps().add(dp);
		}
		if(!this.dps.getDps().isEmpty())
			return true;
		return false;
	}
	
	List<ValueBox> goodValueBoxs=new ArrayList<ValueBox>();//记录来源于一个constant的valuebox，即经过逆向的追踪发现它被赋值为一个constant
	List<ValueBox> badValueBoxs=new ArrayList<ValueBox>();//记录不是来源于constant的ValueBox
	/**
	 * mayConstantDef只判断是否有可能被赋值为constant，即对于一个value由于branch造成的若干处定义，只要由一处为constant就可以
	 * @param unit
	 * @param vb
	 * @param path
	 * @param constantPath
	 * @return
	 */
	private boolean mayConstantDef(Unit unit,ValueBox vb,Path path,List<ValueBox> constantPath){
		if(goodValueBoxs.contains(vb)) return true;
		if(badValueBoxs.contains(vb)) return false;
		if(constantPath.contains(vb)){
			return false;
		}
		
		if(isFindValueBox(vb)){
			goodValueBoxs.add(vb);
			return true;
		}
		List<Unit> tmpDef=new ArrayList<Unit>();
		findDefUnit(unit,vb,new ArrayList<Unit>(),tmpDef);
		boolean flag=false;
		constantPath.add(vb);
		for(Unit tmp:tmpDef){
			//遇到一个函数调用，如果该函数有body，那么进入该body，并以它的ret语句为起点继续迭代遍历
			if(((Stmt)(tmp)).containsInvokeExpr()){
				SootMethod method=((Stmt)(tmp)).getInvokeExpr().getMethod();
				List<Unit> retUnits=new ArrayList<Unit>();
				if(Main.hasBody(method)){
					Path tmpPath=new Path(path);
					tmpPath.getPath().add(tmp);
					for(Unit u:method.getActiveBody().getUnits()){
						if((Stmt)u instanceof JReturnStmt)
							retUnits.add(u);
					}
					for(Unit retUnit:retUnits){
						if(retUnit.getUseBoxes().isEmpty())
							continue;
						List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
						tmpConstantPath.addAll(constantPath);
						if(mayConstantDef(retUnit,retUnit.getUseBoxes().get(0),new Path(tmpPath),tmpConstantPath))
							flag=true;
					}
				}
				else{//如果没有body，以this位置的valuebox为起点继续迭代遍历
					if(((Stmt)tmp).getInvokeExpr().getArgCount()!=0){
						System.out.println("A no-body method called with params in ConstantPropagation(default:false):"+tmp);
					}//有参数的no-body函数处理比较麻烦，目前按false处理
					else if(((Stmt)(tmp)).getInvokeExpr().getUseBoxes().size()==((Stmt)(tmp)).getInvokeExpr().getArgCount())//staticinvoke
					{}//staticinvoke没有this位置的valuebox
					else{
						List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
						tmpConstantPath.addAll(constantPath);
						if(mayConstantDef(tmp,tmp.getUseBoxes().get(0),new Path(path),tmpConstantPath))
							flag=true;
					}
				}
			}
			//遇到filed，确认该filed的值是constant
			else if(((Stmt)(tmp)).containsFieldRef() && Main.defField.containsKey(((Stmt)(tmp)).getFieldRef().getField())){
				for(Unit field:Main.defField.get(((Stmt)(tmp)).getFieldRef().getField())){
					List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
					tmpConstantPath.addAll(constantPath);
					if(mayConstantDef(field,field.getUseBoxes().get(0),new Path(path),tmpConstantPath))
						flag=true;
				}
			}
			//遇到数组
			else if(tmp instanceof JAssignStmt && ((JAssignStmt)tmp).getRightOp() instanceof ArrayRef){
				Value key=((ArrayRef)((JAssignStmt)tmp).getRightOp()).getBase();
				if(!Main.useArray.containsKey(key)) continue;
				List<Unit> ary=Main.useArray.get(key);
				for(Unit aryUnit:ary){
					List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
					tmpConstantPath.addAll(constantPath);
					if(mayConstantDef(aryUnit,aryUnit.getUseBoxes().get(2),new Path(path),tmpConstantPath))
						flag=true;
				}
			}
			//其他情况下，只处理等式右侧只有一个valuebox的情况，包含$i=@this:.....和$i=@param:....这2中情况
			else if(tmp.getUseBoxes().size()==1){
				if(isFindValueBox(tmp.getUseBoxes().get(0))){
					flag=true;
				}
				//确认是否为this，是的话，就以调用该函数的unit为起点
				else if(tmp instanceof IdentityStmt && ((IdentityStmt)tmp).getRightOp() instanceof ThisRef) {
					if(!path.getPath().isEmpty()){//path里记录的是之前遇到的函数调用语句
						Unit callUnit=path.getPath().get(path.getPath().size()-1);
						if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(callUnit)).getInvokeExpr().getArgCount())//staticinvoke
							continue;
						Path tmpPath=new Path(path);
						tmpPath.getPath().remove(path.getPath().size()-1);
						if(mayConstantDef(callUnit,callUnit.getUseBoxes().get(0),tmpPath,constantPath))
							flag=true;
						continue;
					}//若path为空，则所有的caller-unit都是可能的
					for(Unit callUnit:Main.cfg.getCallersOf(Main.cfg.getMethodOf(unit))){
						if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(callUnit)).getInvokeExpr().getArgCount())//staticinvoke
							continue;
						List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
						tmpConstantPath.addAll(constantPath);
						if(mayConstantDef(callUnit,callUnit.getUseBoxes().get(0),new Path(path),tmpConstantPath))
							flag=true;
					}
				}
				else{//确认是否为param，是的话，就以调用该函数的unit为起点
					for(int i=0;i<Main.cfg.getMethodOf(unit).getParameterCount();i++){
						if(vb.getValue().toString()==Main.cfg.getMethodOf(unit).getActiveBody().getParameterLocal(i).getName()){
							if(!path.getPath().isEmpty()){
								Unit callUnit=path.getPath().get(path.getPath().size()-1);
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i++;
								Path tmpPath=new Path(path);
								tmpPath.getPath().remove(path.getPath().size()-1);
								if(mayConstantDef(callUnit,callUnit.getUseBoxes().get(i),tmpPath,constantPath))
									flag=true;
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i--;//把前面加的减掉
								continue;
							}
							for(Unit callUnit:Main.cfg.getCallersOf(Main.cfg.getMethodOf(unit))){
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i++;
								List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
								tmpConstantPath.addAll(constantPath);
								if(mayConstantDef(callUnit,callUnit.getUseBoxes().get(i),new Path(path),tmpConstantPath))
									flag=true;
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i--;
							}
						}
					}
				}
			}
		}
		if(flag) goodValueBoxs.add(vb);
		else badValueBoxs.add(vb);
		return flag;
	}
/**
 * 参见mayConstantDef
 * @param unit
 * @param vb
 * @param path
 * @param constantPath
 * @return
 */
	private boolean mustConstantDef(Unit unit,ValueBox vb,Path path,List<ValueBox> constantPath){
		if(goodValueBoxs.contains(vb)) return true;
		if(badValueBoxs.contains(vb)) return false;
		if(constantPath.contains(vb)){
			return false;
		}
		if(isFindValueBox(vb)){
			goodValueBoxs.add(vb);
			return true;
		}
		List<Unit> tmpDef=new ArrayList<Unit>();
		findDefUnit(unit,vb,new ArrayList<Unit>(),tmpDef);
		boolean flag=true;
		constantPath.add(vb);
		for(Unit tmp:tmpDef){
			if(((Stmt)(tmp)).containsInvokeExpr()){
				SootMethod method=((Stmt)(tmp)).getInvokeExpr().getMethod();
				List<Unit> retUnits=new ArrayList<Unit>();
				if(Main.hasBody(method)){
					Path tmpPath=new Path(path);
					tmpPath.getPath().add(tmp);
					for(Unit u:method.getActiveBody().getUnits()){
						if((Stmt)u instanceof JReturnStmt)
							retUnits.add(u);
					}
					boolean set=false;
					for(Unit retUnit:retUnits){
						if(retUnit.getUseBoxes().isEmpty())
							continue;
						List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
						tmpConstantPath.addAll(constantPath);
						if(!mustConstantDef(retUnit,retUnit.getUseBoxes().get(0),new Path(tmpPath),tmpConstantPath))
							set=true;
					}
					if(set) flag=false;
				}
				else{
					List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
					tmpConstantPath.addAll(constantPath);
					if(((Stmt)(tmp)).getInvokeExpr().getUseBoxes().size()==((Stmt)(tmp)).getInvokeExpr().getArgCount())//staticinvoke
						flag=false;
					else if(((Stmt)tmp).getInvokeExpr().getArgCount()!=0)
						flag=false;
					else if(!mustConstantDef(tmp,tmp.getUseBoxes().get(0),new Path(path),tmpConstantPath))
						flag=false;
				}
			}
			else if(((Stmt)(tmp)).containsFieldRef() && Main.defField.containsKey(((Stmt)(tmp)).getFieldRef().getField())){
				boolean set=false;
				for(Unit field:Main.defField.get(((Stmt)(tmp)).getFieldRef().getField())){
					List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
					tmpConstantPath.addAll(constantPath);
					if(field instanceof JAssignStmt &&!mustConstantDef(field,((JAssignStmt)field).getRightOpBox(),new Path(path),tmpConstantPath))
						set=true;
				}
				if(set) flag=false;
			}
			else if(tmp instanceof JAssignStmt && ((JAssignStmt)tmp).getRightOp() instanceof ArrayRef){
				Value key=((ArrayRef)((JAssignStmt)tmp).getRightOp()).getBase();
				if(!Main.useArray.containsKey(key)) continue;
				List<Unit> ary=Main.useArray.get(key);
				boolean set=false;
				for(Unit aryUnit:ary){
					List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
					tmpConstantPath.addAll(constantPath);
					if(!mustConstantDef(aryUnit,aryUnit.getUseBoxes().get(0),new Path(path),tmpConstantPath))
						set=true;
				}
				if(set) flag=false;
			}
			else if(tmp.getUseBoxes().size()==1){
				if(isFindValueBox(tmp.getUseBoxes().get(0))){
					//flag=true;
				}
				else if(tmp instanceof IdentityStmt && ((IdentityStmt)tmp).getRightOp() instanceof ThisRef) {
					if(!path.getPath().isEmpty()){
						Unit callUnit=path.getPath().get(path.getPath().size()-1);
						if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(callUnit)).getInvokeExpr().getArgCount())//staticinvoke
							continue;
						Path tmpPath=new Path(path);
						tmpPath.getPath().remove(path.getPath().size()-1);
						if(!mustConstantDef(callUnit,callUnit.getUseBoxes().get(0),tmpPath,constantPath))
							flag=false;
						continue;
					}
					boolean set=false;
					for(Unit callUnit:Main.cfg.getCallersOf(Main.cfg.getMethodOf(unit))){
						if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(callUnit)).getInvokeExpr().getArgCount())//staticinvoke
							continue;
						List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
						tmpConstantPath.addAll(constantPath);
						if(!mustConstantDef(callUnit,callUnit.getUseBoxes().get(0),new Path(path),tmpConstantPath))
							set=true;
					}
					if(set) flag=false;
				}
				else{
					for(int i=0;i<Main.cfg.getMethodOf(unit).getParameterCount();i++){
						if(vb.getValue().toString()==Main.cfg.getMethodOf(unit).getActiveBody().getParameterLocal(i).getName()){
							if(!path.getPath().isEmpty()){
								Unit callUnit=path.getPath().get(path.getPath().size()-1);
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i++;
								Path tmpPath=new Path(path);
								tmpPath.getPath().remove(path.getPath().size()-1);
								if(mustConstantDef(callUnit,callUnit.getUseBoxes().get(i),tmpPath,constantPath))
									flag=true;
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i--;
								continue;
							}
							boolean set=false;
							for(Unit callUnit:Main.cfg.getCallersOf(Main.cfg.getMethodOf(unit))){
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i++;
								List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
								tmpConstantPath.addAll(constantPath);
								if(!mustConstantDef(callUnit,callUnit.getUseBoxes().get(i),new Path(path),tmpConstantPath))
									set=true;
								if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(callUnit)).getInvokeExpr().getArgCount())//!staticinvoke
									i--;
							}
							if(set) flag=false;
						}
					}
				}
			}
		}
		if(flag) goodValueBoxs.add(vb);
		else badValueBoxs.add(vb);
		return flag;
	}
	
	
	private boolean isFindValueBox(ValueBox vb){
		String tmpValue=vb.getValue().toString();
		String value;
		Pattern quotPattern=Pattern.compile("\".*\"");
		if(quotPattern.matcher(tmpValue).matches())
			value=tmpValue.substring(1,tmpValue.length()-1);
		else
			value=tmpValue;
		String localValue;
		switch(pattern){
		case 1: localValue=intValue+"";
			    break;
		case 2: localValue=stringValue;
				break;
		case 3: if(booleanValue) localValue="1";
				else localValue="0";
				break;
		case 4: return matchValue.matcher(value).matches();
		case 5: return vb.getValue() instanceof Constant;
		default: return false;
		}
		return value.equals(localValue);
	}
	static List<Unit> badUnits=new ArrayList<Unit>();//记录可以确定的不能到达任意defUnit的unit
	/**
	 * vb来自于一个JAssignStmt的useBoxes
	 * 该函数采用迭代的方法向前遍历，查找vb.getValue()被定义的地方
	 * @param unit 当前遍历的unit，下一条要遍历的unit，是它在程序执行序列上的predecessor
	 * @param vb
	 * @param path 记录遍历的路径，避免出现循环
	 * @param defUnit 记录找到的定义vb.getvalue（）的unit
	 * @return
	 */
	public static  boolean findDefUnit(Unit unit,ValueBox vb,List<Unit> path,List<Unit> defUnit){
		if(path.isEmpty()){
			badUnits.clear();
		}
		//若unit是badUnit，那么它不能到达任意defUnit，直接返回，减少遍历的时间
		if(badUnits.contains(unit)) return !defUnit.isEmpty();
		//若vb.getValue是一个constant，那么就没必要去找它的defUnit了
		if(vb.getValue() instanceof Constant) return !defUnit.isEmpty();
		//遍历到已经遍历过的unit，即出现了循环，返回
		if(path.contains(unit)) return !defUnit.isEmpty();
		path.add(unit);
		SootMethod m=Main.cfg.getMethodOf(unit);
		boolean flag=false;
		if(m.hasActiveBody()){
			List<Unit> pred=Main.cfg.getPredsOf(unit);	
			for(Unit u:Main.cfg.getPredsOf(unit)){
				if(u instanceof IdentityStmt && ((IdentityStmt)u).getLeftOp()==vb.getValue() && ((IdentityStmt)u).getLeftOpBox()!=vb){
					if(!defUnit.contains(u)){ //“到达已经被发现的defUnit”被认为是不可达，即一个defUnit只需要一条可达路径
					defUnit.add(u);
					flag=true;
					}
				}
				else if(u instanceof JAssignStmt && ((JAssignStmt)u).leftBox.getValue()==vb.getValue() && ((JAssignStmt)u).getLeftOpBox()!=vb){
					if(!defUnit.contains(u)){ 
						defUnit.add(u);
						flag=true;
						}
				}
				else {
					List<Unit> tmp=new ArrayList<Unit>();
					tmp.addAll(path);
					int size=defUnit.size();
					findDefUnit(u,vb,tmp,defUnit);
					if(defUnit.size()!=size) flag=true;
				}
			}
		}
		//flag=false表示该unit不能到达任意defUnit
		if(!flag) badUnits.add(unit);
		return !defUnit.isEmpty();
	}
}
