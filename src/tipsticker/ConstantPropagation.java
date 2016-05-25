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
	 * Ĭ�ϲ���mayconstantdef
	 * Ҫ����mustģʽ�Ļ���ʹ�������mustconstantPropagation����
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
	
	List<ValueBox> goodValueBoxs=new ArrayList<ValueBox>();//��¼��Դ��һ��constant��valuebox�������������׷�ٷ���������ֵΪһ��constant
	List<ValueBox> badValueBoxs=new ArrayList<ValueBox>();//��¼������Դ��constant��ValueBox
	/**
	 * mayConstantDefֻ�ж��Ƿ��п��ܱ���ֵΪconstant��������һ��value����branch��ɵ����ɴ����壬ֻҪ��һ��Ϊconstant�Ϳ���
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
			//����һ���������ã�����ú�����body����ô�����body����������ret���Ϊ��������������
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
				else{//���û��body����thisλ�õ�valueboxΪ��������������
					if(((Stmt)tmp).getInvokeExpr().getArgCount()!=0){
						System.out.println("A no-body method called with params in ConstantPropagation(default:false):"+tmp);
					}//�в�����no-body��������Ƚ��鷳��Ŀǰ��false����
					else if(((Stmt)(tmp)).getInvokeExpr().getUseBoxes().size()==((Stmt)(tmp)).getInvokeExpr().getArgCount())//staticinvoke
					{}//staticinvokeû��thisλ�õ�valuebox
					else{
						List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
						tmpConstantPath.addAll(constantPath);
						if(mayConstantDef(tmp,tmp.getUseBoxes().get(0),new Path(path),tmpConstantPath))
							flag=true;
					}
				}
			}
			//����filed��ȷ�ϸ�filed��ֵ��constant
			else if(((Stmt)(tmp)).containsFieldRef() && Main.defField.containsKey(((Stmt)(tmp)).getFieldRef().getField())){
				for(Unit field:Main.defField.get(((Stmt)(tmp)).getFieldRef().getField())){
					List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
					tmpConstantPath.addAll(constantPath);
					if(mayConstantDef(field,field.getUseBoxes().get(0),new Path(path),tmpConstantPath))
						flag=true;
				}
			}
			//��������
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
			//��������£�ֻ�����ʽ�Ҳ�ֻ��һ��valuebox�����������$i=@this:.....��$i=@param:....��2�����
			else if(tmp.getUseBoxes().size()==1){
				if(isFindValueBox(tmp.getUseBoxes().get(0))){
					flag=true;
				}
				//ȷ���Ƿ�Ϊthis���ǵĻ������Ե��øú�����unitΪ���
				else if(tmp instanceof IdentityStmt && ((IdentityStmt)tmp).getRightOp() instanceof ThisRef) {
					if(!path.getPath().isEmpty()){//path���¼����֮ǰ�����ĺ����������
						Unit callUnit=path.getPath().get(path.getPath().size()-1);
						if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(callUnit)).getInvokeExpr().getArgCount())//staticinvoke
							continue;
						Path tmpPath=new Path(path);
						tmpPath.getPath().remove(path.getPath().size()-1);
						if(mayConstantDef(callUnit,callUnit.getUseBoxes().get(0),tmpPath,constantPath))
							flag=true;
						continue;
					}//��pathΪ�գ������е�caller-unit���ǿ��ܵ�
					for(Unit callUnit:Main.cfg.getCallersOf(Main.cfg.getMethodOf(unit))){
						if(((Stmt)(callUnit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(callUnit)).getInvokeExpr().getArgCount())//staticinvoke
							continue;
						List<ValueBox> tmpConstantPath=new ArrayList<ValueBox>();
						tmpConstantPath.addAll(constantPath);
						if(mayConstantDef(callUnit,callUnit.getUseBoxes().get(0),new Path(path),tmpConstantPath))
							flag=true;
					}
				}
				else{//ȷ���Ƿ�Ϊparam���ǵĻ������Ե��øú�����unitΪ���
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
									i--;//��ǰ��ӵļ���
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
 * �μ�mayConstantDef
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
	static List<Unit> badUnits=new ArrayList<Unit>();//��¼����ȷ���Ĳ��ܵ�������defUnit��unit
	/**
	 * vb������һ��JAssignStmt��useBoxes
	 * �ú������õ����ķ�����ǰ����������vb.getValue()������ĵط�
	 * @param unit ��ǰ������unit����һ��Ҫ������unit�������ڳ���ִ�������ϵ�predecessor
	 * @param vb
	 * @param path ��¼������·�����������ѭ��
	 * @param defUnit ��¼�ҵ��Ķ���vb.getvalue������unit
	 * @return
	 */
	public static  boolean findDefUnit(Unit unit,ValueBox vb,List<Unit> path,List<Unit> defUnit){
		if(path.isEmpty()){
			badUnits.clear();
		}
		//��unit��badUnit����ô�����ܵ�������defUnit��ֱ�ӷ��أ����ٱ�����ʱ��
		if(badUnits.contains(unit)) return !defUnit.isEmpty();
		//��vb.getValue��һ��constant����ô��û��Ҫȥ������defUnit��
		if(vb.getValue() instanceof Constant) return !defUnit.isEmpty();
		//�������Ѿ���������unit����������ѭ��������
		if(path.contains(unit)) return !defUnit.isEmpty();
		path.add(unit);
		SootMethod m=Main.cfg.getMethodOf(unit);
		boolean flag=false;
		if(m.hasActiveBody()){
			List<Unit> pred=Main.cfg.getPredsOf(unit);	
			for(Unit u:Main.cfg.getPredsOf(unit)){
				if(u instanceof IdentityStmt && ((IdentityStmt)u).getLeftOp()==vb.getValue() && ((IdentityStmt)u).getLeftOpBox()!=vb){
					if(!defUnit.contains(u)){ //�������Ѿ������ֵ�defUnit������Ϊ�ǲ��ɴ��һ��defUnitֻ��Ҫһ���ɴ�·��
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
		//flag=false��ʾ��unit���ܵ�������defUnit
		if(!flag) badUnits.add(unit);
		return !defUnit.isEmpty();
	}
}
