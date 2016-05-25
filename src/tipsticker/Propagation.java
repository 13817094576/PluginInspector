package tipsticker;
import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import soot.Body;
import soot.Local;
import soot.SootMethod;
import soot.Unit;
import soot.Value;
import soot.ValueBox;
import soot.jimple.ArrayRef;
import soot.jimple.FieldRef;
import soot.jimple.IdentityStmt;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JIfStmt;
import soot.jimple.internal.JStaticInvokeExpr;
import tag.IntTag;
public class Propagation extends Rule{
	private Dps start=new Dps();
	private Dps end=new Dps();
	private String mode;
		
	private List<Path> unsafePaths=new ArrayList<Path>();
	private List<SootMethod> criticalMethods=new ArrayList<SootMethod>();
	private List<SootMethod> hasBody=Main.hasBody;	
	private IInfoflowCFG cfg=Main.cfg;
	private static String PROP_MAY="prop_may";
	private static String PROP_MAYNOT="prop_maynot";
	
	Propagation(Dps s,Dps e,String m){
		this.start.clone(s);
		this.end.clone(e);
		this.mode=m;
	}
	Propagation(){
	}
	
	public Dps getStart(){
		return this.start;
	}
	public Dps getEnd(){
		return this.end;
	}
	
	public boolean isModeMay(){
		if(this.mode.equals(PROP_MAY))
			return true;
		return false;		
	}
	public boolean isModeMayNot(){
		if(this.mode.equals(PROP_MAYNOT))
			return true;
		return false;		
	}
	public String getMode(){
		return this.mode;
	}
	
	public List<Path> getUnsafePaths(){
		return this.unsafePaths;
	}

	public void propagationAnalysis(IInfoflowCFG cfg,List<Propagation> unsafePropagation){
		initMethods();
		if(this.isModeMay()){
			mayAnalysis(cfg);	
		}
		else if(this.isModeMayNot()){
			mayNotAnalysis(cfg);
		}
		pathAndDps();
		if(unsafePropagation!=null)
			unsafePropagation.add(this);
	}
	/**
	 * 先找出所有与start或end相关的method
	 */
	private void initMethods(){
		if(!this.start.getDps().isEmpty()){
			if(((Stmt)(this.start.getDps().get(0).getEp().getUnit())).containsInvokeExpr()){
				criticalMethods.add(((Stmt)(this.start.getDps().get(0).getEp().getUnit())).getInvokeExpr().getMethod());
			}
		}
		if(!this.end.getDps().isEmpty()){
			if(((Stmt)(this.end.getDps().get(0).getEp().getUnit())).containsInvokeExpr()){
				criticalMethods.add(((Stmt)(this.end.getDps().get(0).getEp().getUnit())).getInvokeExpr().getMethod());
			}
		}
	}
//mode:prop_may
	private void mayAnalysis(IInfoflowCFG cfg){
		if(!end.getDps().isEmpty())
		{
			List<Dp> startDps = this.start.getDps();
			for(Dp startDp : startDps)
			{
				Dp endDp=end.getDps().get(0);
				findPath(cfg,startDp.getEp().getUnit(),endDp.getEp().getUnit(),new Path(),-1);	
			}
		}
		//deAnalysis();
	}
//mode:prop_maynot
	private void mayNotAnalysis(IInfoflowCFG cfg){
		mayAnalysis(cfg);
		for(Path path:unsafePaths){
			end.remove(path.getPath().get(path.getPath().size()-1));
		}
	}
	/**
	 * 同步path中的dp和dps中的dp
	 * 因为binds（）存在，导致dps中的dp会消失，所以也要删掉path中与之相关的路径
	 * 反之，同理
	 * @return
	 */
	public boolean pathAndDps(){
		boolean set=false;
		if(this.isModeMay()){
			boolean modifed=false;
			do{
				modifed=false;
				List<Unit> startUnitInPath=new ArrayList<Unit>();
				List<Unit> endUnitInPath=new ArrayList<Unit>();
				for(Path path:unsafePaths){
					startUnitInPath.add(path.getPath().get(0));
					endUnitInPath.add(path.getPath().get(path.getPath().size()-1));
				}
				List<Dp> tmpDps=new ArrayList<Dp>();
				tmpDps.addAll(this.start.getDps());
				List<Unit> startUnitInDps=new ArrayList<Unit>();
				List<Unit> endUnitInDps=new ArrayList<Unit>();
				for(Dp dp:tmpDps){
					if(!startUnitInPath.contains(dp.getEp().getUnit())){
						this.start.getDps().remove(dp);
						modifed=true;
						set=true;
					}
					startUnitInDps.add(dp.getEp().getUnit());
				}
				tmpDps.clear();
				tmpDps.addAll(this.end.getDps());
				for(Dp dp:tmpDps){
					if(!endUnitInPath.contains(dp.getEp().getUnit())){
						this.end.getDps().remove(dp);
						modifed=true;
						set=true;
					}
					endUnitInDps.add(dp.getEp().getUnit());
				}
				List<Path> tmpPaths=new ArrayList<Path>();
				tmpPaths.addAll(unsafePaths);
				for(Path path:tmpPaths){
					if(!startUnitInDps.contains(path.getPath().get(0))){
						unsafePaths.remove(path);
						modifed=true;
						set=true;
					}
					if(!endUnitInDps.contains(path.getPath().get(path.getPath().size()-1))){
						unsafePaths.remove(path);
						modifed=true;
						set=true;
					}
				}
			}while(modifed);
		}
		else if(this.isModeMayNot()){
			List<Unit> endUnitInPath=new ArrayList<Unit>();
			for(Path path:unsafePaths){
				endUnitInPath.add(path.getPath().get(path.getPath().size()-1));
			}
			List<Dp> tmp=new ArrayList<Dp>();
			tmp.addAll(this.end.getDps());
			end.getDps().clear();
			for(Dp dp:tmp){
				if(endUnitInPath.contains(dp.getEp().getUnit()))
					end.getDps().add(dp);
				else
					set=true;
			}
		}
		return set;
	}

	public void removeEmptyPath(){
		List<Path> tmp=new ArrayList<Path>();
		tmp.addAll(unsafePaths);
		unsafePaths.clear();
		for(Path path:tmp){
			if(!path.getPath().isEmpty())
				unsafePaths.add(path);
		}
	}

//find the list of units used ValueBox vb until its value is redefined.
	public static boolean findUseUnit(IInfoflowCFG cfg,Body b,ValueBox vb,List<Unit> useUnit){
		Unit defUnit=null;
		if(vb==null)
			return false;
		for(Unit unit:b.getUnits()){
			if(unit.getDefBoxes().contains(vb)){// find startUnit which is  the unit defined ValueBox vb
				defUnit=unit;
				break;
			}
		}
		if(defUnit==null){
			for(Unit unit:b.getUnits()){
				if(unit.getUseBoxes().contains(vb)){// find startUnit which is  the unit used ValueBox vb
					defUnit=unit;
					break;
				}
			}
		}
		if(defUnit==null)
			return false;
//		if(defUnit instanceof JAssignStmt && ((JAssignStmt)defUnit).getLeftOp() instanceof ArrayRef){
//			Value key=((ArrayRef)((JAssignStmt)defUnit).getLeftOp()).getBase();
//			useUnit.addAll(Main.useArray.get(key));
//			
//		}
		
		if(!((Stmt)(defUnit)).containsFieldRef()||!defUnit.getDefBoxes().contains(((Stmt)(defUnit)).getFieldRefBox())){
			for(Unit unit:cfg.getSuccsOf(defUnit)){
				Unit tmp=unit;
				findUseUnitLoop(cfg,tmp,vb,useUnit,new ArrayList<Unit>());
			}
		}
		else{
			if(!Main.useField.keySet().contains(((Stmt)(defUnit)).getFieldRef().getField()))
				return false;
			useUnit.addAll(Main.useField.get(((Stmt)(defUnit)).getFieldRef().getField()));
		}
		return !useUnit.isEmpty();
		
	}
	private static boolean findUseUnitLoop(IInfoflowCFG cfg,Unit a,ValueBox vb,List<Unit> useUnit,List<Unit>noneUseUnit){
		if((a.getDefBoxes().size()!=0)&&a.getDefBoxes().get(0).getValue()==vb.getValue()){// redefine the value of vb,then it is endUnit
			boolean set=false;
			for(ValueBox tmpVb:a.getUseBoxes()){
				if(tmpVb.getValue()==vb.getValue())
					set=true;
			}
			if(!set) return !useUnit.isEmpty();
		}	
		if(noneUseUnit.contains(a))
			return !useUnit.isEmpty();
		boolean set=false;
		for(ValueBox v:a.getUseBoxes()){
			if((v.getValue()==vb.getValue())
				||(vb.getValue() instanceof ArrayRef && vb.getValue().toString().equals(v.getValue().toString()))){
				set=true;
				if(useUnit.contains(a)) return !useUnit.isEmpty();
				useUnit.add(a);
			}
		}
		if(!set) noneUseUnit.add(a);
		for(Unit unit:cfg.getSuccsOf(a)){
			findUseUnitLoop(cfg,unit,vb,useUnit,noneUseUnit);
		}
		if(useUnit.isEmpty()) return false;
		if((a.getDefBoxes().size()!=0)&&a.getDefBoxes().get(0).getValue()==vb.getValue())// redefine the value of vb,then it is endUnit
			return !useUnit.isEmpty();
		return true;
	}

		List<Unit> badUnits=new ArrayList<Unit>();//已经确定的不能到达任意end的unit
		/**
		 * 查找在start和end之间是否存在一条数据传输路径
		 * @param cfg
		 * @param start
		 * @param end
		 * @param path 记录传播路径
		 * @param containIndex 用来判断遍历时是否出现循环
		 * @return
		 */
	private boolean findPath(IInfoflowCFG cfg,Unit start,Unit end,Path path,int containIndex){
		if(path.getPath().contains(start)||badUnits.contains(start)){
			return false;
		}
		for(Path localPath:unsafePaths){
			if(localPath.getPath().get(0)==start&&localPath.getPath().get(localPath.getPath().size()-1)==end)
				return true;
		}
		if(!indexContain(start,path,containIndex)) return false;
		if(start==end){//到达end，可以确认一条path
			Path localPath=new Path(path);
			localPath.getPath().add(start);
			if(!isContainPath(localPath)&&isRealEnd(path,start))
				this.unsafePaths.add(localPath);
			return true;
		}
		if(this.end.contains(start)){//到达了其他的end
			Path localPath=new Path(path);
			localPath.getPath().add(start);
			if(!isContainPath(localPath)&&isRealEnd(path,start))
				this.unsafePaths.add(localPath);
			return true;
		}
			
		path.getPath().add(start);
		List<Unit> directUseUnits=new ArrayList<Unit>();
		
		SootMethod method = cfg.getMethodOf(start);
		
		Body b=method.getActiveBody();
		ValueBox vbStart=null;
		if(!start.getDefBoxes().isEmpty())
			vbStart=start.getDefBoxes().get(0);
		else{
			if(!((Stmt)(start)).containsInvokeExpr()||((Stmt)start).getInvokeExpr() instanceof JStaticInvokeExpr){
				return false;
			}
			vbStart=start.getUseBoxes().get(0);
		}
		if(!findUseUnit(cfg,b,vbStart,directUseUnits)){
			return false;
		}
		boolean flag=false;
		for(Unit unit:directUseUnits){//以使用了该value的useUnit为下一条要遍历的unit
			if(this.end.contains(unit)){
				if(!isRealEnd(path,unit)) continue;
				Path localPath=new Path(path);
				localPath.getPath().add(unit);
				if(!isContainPath(localPath))
					this.unsafePaths.add(localPath);
				flag=true;
				if(Main.OneSorceOnePath && flag) return true;
				continue;
			}
			if(((Stmt)unit)instanceof JIfStmt){ 
				if(Main.OneSorceOnePath && flag) return true;
				continue;
			}
			else if(unit instanceof JAssignStmt 
					&& ((JAssignStmt)unit).getLeftOp() instanceof FieldRef 
					&& Main.useField.containsKey(((Stmt)(unit)).getFieldRef().getField())){
				for(Unit startUnit:Main.useField.get(((Stmt)(unit)).getFieldRef().getField())){
					Path tmpPath=new Path(path.getPath());
					int index=containIndex;
					if(!indexContain(unit,tmpPath,index)){
						if(Main.OneSorceOnePath && flag) return true;
						continue;
					}
					tmpPath.getPath().add(unit);
					if(findPath(cfg,startUnit,end,tmpPath,index)){
						flag=true;
						if(Main.OneSorceOnePath && flag) return true;
						continue;
					}
				}
			}
			else if(unit instanceof JAssignStmt && ((JAssignStmt)unit).getLeftOp() instanceof ArrayRef){
				Value key=((ArrayRef)((JAssignStmt)unit).getLeftOp()).getBase();
				if(!Main.useArray.containsKey(key)){ 
					if(Main.OneSorceOnePath && flag) return true;
					continue;
				}
				List<Unit> ary=Main.useArray.get(key);
				for(Unit aryUnit:ary){
					Path tmpPath=new Path(path.getPath());
					int index=containIndex;
					if(!indexContain(unit,tmpPath,index)) {
						if(Main.OneSorceOnePath && flag) return true;
						continue;
					}
					if(unit!=aryUnit)
						tmpPath.getPath().add(unit);
					if(findPath(cfg,aryUnit,end,tmpPath,index)){
						flag=true;
						if(Main.OneSorceOnePath && flag) return true;
						continue;
					}
				}
			}
			else if(((Stmt)(unit))instanceof ReturnStmt){
				if(path.getPath().contains(unit))
					containIndex=path.getPath().indexOf(unit);
				else
					containIndex=-1;
				Unit callUnit=path.lastCall(cfg,this.criticalMethods);
				if(callUnit!=null){
					Path tmpPath=new Path(path.getPath());
					int index=containIndex;
					if(!indexContain(unit,tmpPath,index)){
						if(Main.OneSorceOnePath && flag) return true;
						continue;
					}
					tmpPath.getPath().add(unit);
					flag=findPath(cfg,callUnit,end,tmpPath,containIndex);
					if(Main.OneSorceOnePath && flag) return true;
					continue;
				}
				else{
					Set<Unit> methodUnits=cfg.getCallersOf(method);
					int index=containIndex;
					if(!indexContain(unit,path,index)){
						if(Main.OneSorceOnePath && flag) return true;
						continue;
					}
					Path tmpPath=new Path(path.getPath());
					tmpPath.getPath().add(unit);
					for(Unit mUnit:methodUnits){
						if(findPath(cfg,mUnit,end,tmpPath,containIndex)){
							flag=true;
							if(Main.OneSorceOnePath && flag) return true;
							continue;
						}
					}
				}
			}
			else if(((Stmt)(unit)).containsInvokeExpr()){
				if(path.getPath().contains(unit))
					containIndex=path.getPath().indexOf(unit);
				else
					containIndex=-1;
				path.getPath().add(unit);
				List<Integer> paramNumAry=new ArrayList<Integer>();
				Integer num=0;
				if(((Stmt)(unit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(unit)).getInvokeExpr().getArgCount())//staticinvoke
					num=1;
				for(ValueBox vb:((Stmt)(unit)).getInvokeExpr().getUseBoxes()){
					if(vb.getValue()==vbStart.getValue())
						paramNumAry.add(num);
					num++;
				}
				SootMethod subMethod=((Stmt)(unit)).getInvokeExpr().getMethod();
//---------------------------------------------------------------------
//no active body
				if(!hasBody.contains(subMethod)){
					if(((Stmt)(unit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(unit)).getInvokeExpr().getArgCount() 
							&& unit.getDefBoxes().isEmpty())
					{
						//staticinvoke
						if(Main.OneSorceOnePath && flag) return true;
						continue;
					}
					//	return false;
					path.getPath().remove(unit);
					Path tmpPath=new Path(path.getPath());
					if(findPath(cfg,unit,end,tmpPath,containIndex)){
						flag=true;
					}
					if(Main.OneSorceOnePath && flag) return true;
				}
//--------------------------------------------------------------------
//has active body
				else{
					Body subBody=subMethod.getActiveBody();
					boolean set=false;
					for(Integer paramNum:paramNumAry){
						if(Main.OneSorceOnePath && set) break;
						Local subLocal=null;
						if(paramNum!=0){
							subLocal=subBody.getParameterLocal(paramNum-1);
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
						Path tmpPath=new Path(path.getPath());
						if(findPath(cfg,defUnit,end,tmpPath,containIndex))
						set=true;
					}
					path.getPath().remove(unit);
				if(set){
					flag=true;
				}
				if(Main.OneSorceOnePath && flag) return true;
				}
			}
			else {
				Path tmpPath=new Path(path.getPath());
				if(findPath(cfg,unit,end,tmpPath,containIndex)){
					flag=true;
					if(Main.OneSorceOnePath && flag) return true;
					continue;
				}
			}			
		}
		if(!flag) badUnits.add(start);
		return flag;
	}
	//判断unit是否可以作为该path的终止结点
	//正常情况下，终止结点的某个参数应该接受前一节点传来的数据(一般为前一节点的defBox,或者useBox[0])，该参数由此unit对应的dp.getArgNum()给出
	private boolean isRealEnd(Path path,Unit unit){
		if(path.getPath().isEmpty()) return true;
		Unit pre=path.getPath().get(path.getPath().size()-1);
		if(!(pre instanceof IdentityStmt) && !(pre instanceof JAssignStmt)){
			if(((Stmt)pre).containsInvokeExpr()||((Stmt)(pre)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(pre)).getInvokeExpr().getArgCount()){
					if(((Stmt)(unit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(unit)).getInvokeExpr().getArgCount()&&unit.getUseBoxes().get(this.end.getArgNum()-1).getValue()==pre.getUseBoxes().get(0).getValue())
						return true;
					if(((Stmt)(unit)).getInvokeExpr().getUseBoxes().size()!=((Stmt)(unit)).getInvokeExpr().getArgCount()&&unit.getUseBoxes().get(this.end.getArgNum()).getValue()==pre.getUseBoxes().get(0).getValue())
						return true;			
			}
			return false;
		}
		boolean realEnd=true;
		if(!((Stmt)(unit)).containsInvokeExpr()) realEnd=false;
		if(((Stmt)(unit)).getInvokeExpr().getUseBoxes().size()==((Stmt)(unit)).getInvokeExpr().getArgCount()){//StaticInvoke
			if(this.end.getArgNum()<1||unit.getUseBoxes().get(this.end.getArgNum()-1).getValue()!=pre.getDefBoxes().get(0).getValue())
				realEnd=false;
		}
		else if(unit.getUseBoxes().size()<this.end.getArgNum()+1)
			realEnd=false;
		else if(unit.getUseBoxes().get(this.end.getArgNum()).getValue()!=pre.getDefBoxes().get(0).getValue())
			realEnd=false;
		return realEnd;
	}
	//判断path是否出现循环
	//如果list的第（index+1）个unit等于start，即认为出现循环，返回false
	//index保存的是-1或者某个索引游标，该游标指向相对于start前一条语句在path中出现的位置，未出现即为-1
	private boolean indexContain(Unit start,Path path,int index){
		if (index==-1)
		{
			if (path.getPath().contains(start))
			{
				index=path.getPath().indexOf(start);
			}
		}
		else
		{
			if (path.getPath().size() > (index+1) 					// Prevent access violation
					&& path.getPath().get(index+1) == start)
			{
				return false;
			}
			
			if (path.getPath().contains(start))
			{
				index=path.getPath().indexOf(start);
			}
			else 
			{
				index=-1;
			}
		}
		return true;
	}
	//找出start中继续向后传递的valuebox
	//若start为赋值语句，则返回defineBox
	//若start为staticInvoke，则返回this对应的valuebox
	private ValueBox getValueBox(Unit start){
		ValueBox vbStart=null;
		if(!start.getDefBoxes().isEmpty())
			vbStart=start.getDefBoxes().get(0);
		else{
			if(!((Stmt)(start)).containsInvokeExpr()){
				return null;
			}
			int useBoxSize=start.getUnitBoxes().size();
			int argCount=((Stmt)(start)).getInvokeExpr().getArgs().size();
			if(useBoxSize-1>argCount)
				vbStart=start.getUseBoxes().get(0);
			else{
				return null;
			}
		}
		return vbStart;
	}
	
	private boolean isContainPath(Path path){
		for(Path unsafePath:unsafePaths){
			boolean set=false;
			if(unsafePath.getPath().size()==path.getPath().size()){
				for(int i=0;i<path.getPath().size();i++){
					if(path.getPath().get(i)!=unsafePath.getPath().get(i))
						set=true;
				}
				if(!set) return true;
			}
		}
		return false;
	}
	
	public boolean isEmpty(){
		return this.start.getDps().isEmpty();
	}
	public void clear(){
		this.start.getDps().clear();
		this.end.getDps().clear();
	}
	
	List<Dp> badDp=new ArrayList<Dp>();
	List<DataExecution> dataExecution=new ArrayList<DataExecution>();
	private boolean findPath2(Dp start,Dp end){
		if(start.isEqual(end))
			return true;
		
		return true;
	}
	
	private List<Dp> findUseDp(Dp start,Unit now){
		List<Dp> useDp=new ArrayList<Dp>();
		Unit s=start.getEp().getUnit();
		SootMethod m=cfg.getMethodOf(s);
		if(Main.hasBody(m)){
			Value v=start.getValue();
			if(v!=null){
				for(Unit succs:cfg.getSuccsOf(now)){
					if(unitUseValue(succs,v)){
						Dp tmp=new Dp(succs,getArgIndex(succs,v));
						useDp.add(tmp);
					}
					else if(unitDefValue(succs,v))
						continue;
					else{
						useDp.addAll(findUseDp(start,succs));
					}
				}
			}
		}
		return useDp;
	}
	private boolean unitUseValue(Unit s,Value v){
		for(ValueBox vb:s.getUseBoxes()){
			if(vb.getValue()==v)
				return true;
		}
		return false;
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
	private boolean unitDefValue(Unit s,Value v){
		if(s instanceof JAssignStmt || s instanceof JIdentityStmt)
			if(s.getDefBoxes().get(0).getValue().toString().equals(v.toString()))
				return true;
		return false;
	}
	
	public void deAnalysis(){
		if(end.getDps().isEmpty())
			return;
		for(Dp startDp:start.getDps()){
			DataExecution de=new DataExecution(startDp,startDp.getValue(),startDp.getEp().getUnit(),end);
			List<DataExecution> family=new ArrayList<DataExecution>();
			family.add(de);
			List<DataExecution> mirror=new ArrayList<DataExecution>();
			mirror.addAll(family);
			List<DataExecution> reachEnd=new ArrayList<DataExecution>();
			boolean live=true;
			while(live){
				live=false;
				family.clear();
				List<DataExecution> deadDE=new ArrayList<DataExecution>();
				for(DataExecution deMirror:mirror){
					if(deMirror.isliving())
						live=true;
					if(deMirror.isreachEnd())
						reachEnd.add(deMirror);
					if(deMirror.isdead())
						deadDE.add(deMirror);
					family.addAll(deMirror.breed());
				}
				mirror.clear();
//				bad.clear();
//				good.clear();
//				for(DataExecution member:family){
//					bad.addAll(member.getBadUnit());
//				}
//				for(Unit badUnit:findBadUnits(deadDE)){
//					if(!bad.contains(badUnit))
//						bad.add(badUnit);
//				}
//				for(DataExecution member:family){
//					member.getBadUnit().clear();
//					member.getBadUnit().addAll(bad);
//				}
				mirror.addAll(family);
			}
			for(DataExecution member:reachEnd){
				Path path=new Path();
				for(Dp dp:member.getPath())
					path.getPath().add(dp.getEp().getUnit());
				if(notContainPath(unsafePaths,path))
					unsafePaths.add(path);
			}
		}
	}
	private boolean notContainPath(List<Path> unsafe,Path path){
		for(Path local:unsafe){
			if(local.isEqual(path))
				return false;
		}
		return true;
	}
	List<Unit> bad=new ArrayList<Unit>();
	List<Unit> good=new ArrayList<Unit>();
	private List<Unit> findBadUnits(List<DataExecution> dead){
		List<Unit> badUnits=new ArrayList<Unit>();
		List<Unit> total=new ArrayList<Unit>();
		for(DataExecution de:dead){
			total.addAll(de.getPropagationPath());
		}
		for(Unit unit:total){
			if(isBad(total,unit))
				badUnits.add(unit);
		}
		return badUnits;
	}
	
	private boolean isBad(List<Unit> total,Unit unit){
		if(bad.contains(unit)) return true;
		if(good.contains(unit)) return false;
		boolean set=false;
		if(!total.containsAll(cfg.getSuccsOf(unit))){
			good.add(unit);
			return false;
		}
		for(Unit succs:cfg.getSuccsOf(unit)){
				if(!isBad(total,succs)) set=true;
		}
		if(set){
			good.add(unit);
			return false;
		}
		return true;
	}
		
	
	
}
