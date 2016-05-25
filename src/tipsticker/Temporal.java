package tipsticker;

import java.util.ArrayList;
import java.util.HashMap;
import java.util.Iterator;
import java.util.List;
import java.util.Set;

import soot.Scene;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.toolkits.callgraph.CallGraph;
import soot.jimple.toolkits.callgraph.Edge;
public class Temporal extends Rule{
	private Eps start=new Eps();
	private Eps pass=new Eps();
	private Eps end=new Eps();
	private String mode;
	
	
	private Eps tmpStart=new Eps();
	private Eps tmpEnd=new Eps();
	
	private List<Path> unsafePaths=new ArrayList<Path>();
	private HashMap<SootMethod,List<Unit>> map=new HashMap<SootMethod,List<Unit>>();
	
	private static String PROP_PASS_THROUGH="prop_pass_through";
	private static String PROP_SKIP="prop_skip";
	
	Temporal(Eps s,Eps p,Eps e,String m){
		this.start.clone(s);
		this.pass.clone(p);
		this.end.clone(e);
		this.mode=m;
	}
	Temporal(){
	}
	
	public Eps getStart(){
		return this.start;
	}
	public Eps getPass(){
		return this.pass;
	}
	public Eps getEnd(){
		return this.end;
	}
	public String getMode(){
		return this.mode;
	}
	public List<Path> getUnsafePaths(){
		return this.unsafePaths;
	}
	public boolean isModeThrough(){
		if(this.mode.equals(PROP_PASS_THROUGH))
			return true;
		return false;
		
	}
	public boolean isModeSkip(){
		if(this.mode.equals(PROP_SKIP))
			return true;
		return false;              
	}
	

// if Ep start pass and end are in the same method body,then return true. 
	public void temporalAnalysis(IInfoflowCFG cfg,List<Temporal> unsafeTemporal){
		initMap(cfg);
		if(this.isModeThrough()){
		 throughAnalysis(cfg);
		}
		else if(this.isModeSkip()){
			skipAnalysis(cfg);
		}
		if(unsafeTemporal!=null)
			unsafeTemporal.add(this);
		pathAndEps();
	}
//
	private boolean skipAnalysis(IInfoflowCFG cfg){
		workList.clear();
		workList.addAll(startList);
		for(Unit start:startList){
			workList.remove(start);
			Path path=new Path();
			findPath(cfg,start,path,-1);	
			workList.add(start);
		}
		List<Path> tmp=new ArrayList<Path>();
		tmp.addAll(unsafePaths);
		for(Path unsafepath:tmp){
			boolean set=true;
			for(Unit pathUnit:unsafepath.getPath()){
				if(passList.contains(pathUnit)){
						set=false;
				}
			}
			if(!set) unsafePaths.remove(unsafepath);
		}
		return !unsafePaths.isEmpty();
	}
	private boolean throughAnalysis(IInfoflowCFG cfg){
		workList.clear();
		workList.addAll(startList);
		for(Unit start:startList){
			workList.remove(start);
			Path path=new Path();
			findPath(cfg,start,path,-1);	
			workList.add(start);
		}
		List<Path> tmp=new ArrayList<Path>();
		tmp.addAll(unsafePaths);
		for(Path unsafepath:tmp){
			boolean set=true;
			for(Unit pathUnit:unsafepath.getPath()){
				if(passList.contains(pathUnit)){
						set=false;
				}
			}
			if(set) unsafePaths.remove(unsafepath);
		}
		return !unsafePaths.isEmpty();
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
	
	private boolean unitIntersection(List<Unit>unitInPath,List<Unit>unitInEps){
		List<Unit> tmp1=new ArrayList<Unit>();
		List<Unit> tmp2=new ArrayList<Unit>();
		tmp1.addAll(unitInPath);
		tmp2.addAll(unitInEps);
		unitInPath.clear();
		unitInEps.clear();
		for(Unit unit:tmp1){
			if(tmp2.contains(unit)){
				unitInPath.add(unit);
				unitInEps.add(unit);
			}
		}
		for(Unit unit:tmp2){
			if(tmp1.contains(unit)){
				if(!unitInPath.contains(unit)){
					unitInPath.add(unit);
					unitInEps.add(unit);
				}
			}
		}
		if(unitInPath.size()==tmp1.size()&&unitInEps.size()==tmp2.size())
			return false;
		return true;
	}
	private void epsIntersection(Eps eps,List<Unit>unitInEps){
		Eps tmp1=new Eps(eps.getEps());
		eps.getEps().clear();
		List<Unit> tmp2=new ArrayList<Unit>();
		tmp2.addAll(unitInEps);
		unitInEps.clear();
		for(Ep ep:tmp1.getEps()){
			if(tmp2.contains(ep.getUnit())){
				eps.getEps().add(ep);
				unitInEps.add(ep.getUnit());
			}
		}
		for(Unit unit:tmp2){
			if(tmp1.contains(unit)){
				if(!unitInEps.contains(unit)){
					unitInEps.add(unit);
					eps.getEps().add(eps.getEp(unit));
				}
			}
		}
	}
	private void pathStartIntersection(List<Unit> startInPath){
		for(Path path:unsafePaths){
			if(!startInPath.contains(path.getPath().get(0)))
				path.getPath().clear();
		}
		List<Unit> tmp=new ArrayList<Unit>();
		tmp.addAll(startInPath);
		startInPath.clear();
		for(Path path:unsafePaths){
			if(!path.getPath().isEmpty())
				startInPath.add(path.getPath().get(0));
		}
	}
	private void pathPassIntersection(List<Unit> passInPath){
		List<Unit> tmp=new ArrayList<Unit>();
		tmp.addAll(passInPath);
		passInPath.clear();
		for(Unit unit:passInPath){
			boolean set=false;
			for(Path path:unsafePaths){
				if(path.getPath().contains(unit));
				set=true;
			}
			if(set) passInPath.add(unit);
		}
		for(Path path:unsafePaths){
			boolean set=false;
			for(Unit unit:passInPath){
				if(path.getPath().contains(unit))
					set=true;
			}
			if(!set) path.getPath().clear();
		}
	}
	private void pathEndIntersection(List<Unit> endInPath){
		for(Path path:unsafePaths){
			if(!endInPath.contains(path.getPath().get(path.getPath().size()-1)))
				path.getPath().clear();
		}
		List<Unit> tmp=new ArrayList<Unit>();
		tmp.addAll(endInPath);
		endInPath.clear();
		for(Path path:unsafePaths){
			if(!path.getPath().isEmpty())
				endInPath.add(path.getPath().get(0));
		}
	}
	public boolean pathAndEps(){
		initUnitList();
		boolean set=false;
		List<Unit> startInPath=new ArrayList<Unit>();
		List<Unit> passInPath=new ArrayList<Unit>();
		List<Unit> endInPath=new ArrayList<Unit>();
		for(Path path:unsafePaths){
			startInPath.add(path.getPath().get(0));
			endInPath.add(path.getPath().get(path.getPath().size()-1));
		}
		if(this.isModeThrough()){
			for(Path path:unsafePaths){
				for(Unit passUnit:path.getPath()){
					if(passList.contains(passUnit))
						passInPath.add(passUnit);
				}
			}
			boolean modified=true;
			while(modified){
				modified=false;
				if(unitIntersection(startInPath,startList)){
					modified=true;
					set=true;
					epsIntersection(start,startList);
					pathStartIntersection(startInPath);
				}
				if(unitIntersection(passInPath,passList)){
					modified=true;
					set=true;
					epsIntersection(pass,passList);
					pathPassIntersection(passInPath);
				}
				if(unitIntersection(endInPath,endList)){
					modified=true;
					set=true;
					epsIntersection(end,endList);
					pathEndIntersection(endInPath);
				}
			}		
		}
		else if(this.isModeSkip()){
			boolean modified=true;
			while(modified){
				modified=false;
				if(unitIntersection(startInPath,startList)){
					modified=true;
					set=true;
					epsIntersection(start,startList);
					pathStartIntersection(startInPath);
				}
				if(unitIntersection(endInPath,endList)){
					modified=true;
					set=true;
					epsIntersection(end,endList);
					pathEndIntersection(endInPath);
				}
			}
		}
		return set;
	}
	
		List<Unit> startList=new ArrayList<Unit>();
		List<Unit> passList=new ArrayList<Unit>();
		List<Unit> endList=new ArrayList<Unit>();
		List<Unit> workList=new ArrayList<Unit>();
	private boolean findPath(IInfoflowCFG cfg,Unit start,Path path,int containIndex){
		SootMethod method=cfg.getMethodOf(start);
		if(!map.keySet().contains(method))
			return false;
		if(containIndex>=0&&path.getPath().contains(start)){
			if(containIndex!=path.getPath().indexOf(start)-1)
				containIndex=path.getPath().indexOf(start);
			else return false;
		}
		else if(path.getPath().contains(start))
			 containIndex=path.getPath().indexOf(start);
		else containIndex=-1;
		if(workList.contains(start))
			return false;
		if(endList.contains(start)){
			path.getPath().add(start);
			unsafePaths.add(path);
			return true;
		}
		path.getPath().add(start);
		if(((Stmt)(start)).containsInvokeExpr()){
			if(map.keySet().contains(((Stmt)(start)).getInvokeExpr().getMethod())){
				boolean set=false;
				for(Unit startUnit:cfg.getStartPointsOf(((Stmt)(start)).getInvokeExpr().getMethod())){
					Path tmpPath = new Path(path.getPath());
					if(findPath(cfg,startUnit,tmpPath,containIndex)){
						set=true;
						break;
					}
				}
				if(set) return set;
			}
		}
		else if(((Stmt)(start))instanceof ReturnStmt){
			path.getPath().remove(start);
			Unit callUnit=path.lastCall(cfg,map.keySet());
			path.getPath().add(start);
			if(callUnit!=null){
//				if(!path.isCallPairToRet(cfg, callUnit, start))
//					return false;
				List<Unit> subPath=path.getPath().subList(path.getPath().indexOf(callUnit), path.getPath().size()-1);
				List<Unit> tmpSubPath=new ArrayList<Unit>();
				tmpSubPath.addAll(subPath);
				path.getPath().removeAll(subPath);
				path.getPath().remove(path.getPath().size()-1);
				path.getPath().add(callUnit);
				for(Unit subPathUnit:tmpSubPath){
					if(passList.contains(subPathUnit))
						path.getPath().add(subPathUnit);
				}
				path.getPath().add(start);
				boolean set=false;
				for(Unit startUnit:cfg.getSuccsOf(callUnit)){
					Path tmpPath = new Path(path.getPath());
					if(findPath(cfg,startUnit,tmpPath,containIndex)){
						set=true;
						break;
					}
				}
				return set;
			}
			else{
				Set<Unit> startUnits=cfg.getCallersOf(method);
				boolean set=false;
				for(Unit startUnit:startUnits){
					Path tmpPath = new Path(path.getPath());
					if(findPath(cfg,startUnit,tmpPath,containIndex)){
						set=true;
						break;
					}
				}
				return set;
			}
		}
		boolean set=false;
		for(Unit startUnit:cfg.getSuccsOf(start)){
			Path tmpPath = new Path(path.getPath());
			if(findPath(cfg,startUnit,tmpPath,containIndex)){
				set=true;
				break;
			}
		}
		return set;
	}
	
	private void initUnitList(){
		startList.clear();
		passList.clear();
		endList.clear();
		workList.clear();
		for(Ep startEp:this.start.getEps()){
			startList.add(startEp.getUnit());
		}
		for(Ep passEp:this.pass.getEps()){
			passList.add(passEp.getUnit());
		}
		for(Ep endEp:this.end.getEps()){
			endList.add(endEp.getUnit());
		}
		workList.addAll(startList);
		workList.addAll(passList);
		workList.addAll(endList);
	}
	private boolean initMap(IInfoflowCFG cfg){
		CallGraph cg=Scene.v().getCallGraph();
		initUnitList();
		for(Unit unit:workList){
			SootMethod method=cfg.getMethodOf(unit);
			if(map.containsKey(method))
				map.get(method).add(unit);
			else{
				List<Unit> tmp1=new ArrayList<Unit>();
				tmp1.add(unit);
				map.put(method, tmp1);
				List<SootMethod> loopMethods=new ArrayList<SootMethod>();
				loopMethods.add(method);
				while(!loopMethods.isEmpty()){
					List<SootMethod> tmpMethods=new ArrayList<SootMethod>();
					tmpMethods.addAll(loopMethods);
					Iterator<Edge> edges=cg.edgesInto(tmpMethods.get(0));
					tmpMethods.remove(0);
					while(edges.hasNext()){
						SootMethod fatherMethod=edges.next().src();
						tmpMethods.add(fatherMethod);
						if(map.containsKey(fatherMethod))
							map.get(fatherMethod).add(unit);
						else{
							List<Unit> tmp2=new ArrayList<Unit>();
							tmp2.add(unit);
							map.put(fatherMethod, tmp2);
						}
					}
					loopMethods=tmpMethods;
				}
			}
		}
		if(this.map.isEmpty())
			return false;
		return true;
	}
	

	public boolean isEmpty(){
		return this.start.getEps().isEmpty();
	}
	public void clear(){
		this.start.getEps().clear();
		this.pass.getEps().clear();
		this.end.getEps().clear();
	}

}
//
	
