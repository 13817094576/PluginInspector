package tipsticker;

import java.util.ArrayList;
import java.util.List;
import java.util.Set;

import soot.SootMethod;
import soot.Unit;
import soot.jimple.ReturnStmt;
import soot.jimple.Stmt;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import tag.IntTag;

public class Path {
	private List<Unit> path=new ArrayList<Unit>();
	
	Path(){
	}
	Path(List<Unit> path){
		this.path.addAll(path);
	}
	Path(Path p){
		this.path.addAll(p.getPath());
	}
	
	public List<Unit> getPath(){
		return this.path;
	}
	public void setPath(List<Unit> path){
		this.path=path;
	}
	public String toString(){
		String str="";
		for(Unit unit:path){
			str+=unit.toString();
			str+=" unitNum:";
			str+=((IntTag)(unit.getTag("unitNum"))).getIntValue();
			str+="\n";
		}
		return str;
	}
	public boolean isEqual(Path p){
		if(this.path.size()!=p.getPath().size())
			return false;
		for(int i=0;i<path.size();i++){
			if(path.get(i)!=p.getPath().get(i))
				return false;
		}
		return true;
	}
	/**
	 * ����2��lastcall������Ϊ���ҵ�ret����Ӧ��caller���
	 * ��dataflowanalysis�Ĺ����У�������ret��䷵�غ�Ӧ��app�ж�λ�������ص���λ��
	 * ���õ�������stack�ķ���
	 * ����һ��method call���ͽ�����ջ������һ��ret�ͳ�ջ
	 * @param cfg
	 * @param methods
	 * @return
	 */
	public Unit lastCall(IInfoflowCFG cfg,Set<SootMethod> methods){
		Unit lastCall=null;
		Unit lastRet=null;
		int callIndex=callStack(methods).size()-1;
		int retIndex=retStack().size()-1;
		while(callIndex>=0){
			lastCall=callStack(methods).get(callIndex);
			if(retIndex<0) return lastCall;
			lastRet=retStack().get(retIndex--);
			if(isCallPairToRet(cfg,lastCall,lastRet))
				callIndex--;
			else{
				return lastCall;
			}
		}
		return lastCall;
	}
	public Unit lastCall(IInfoflowCFG cfg,List<SootMethod> methods){
		Unit lastCall=null;
		Unit lastRet=null;
		int callIndex=callStack(methods).size()-1;
		int retIndex=retStack().size()-1;
		while(callIndex>=0){
			lastCall=callStack(methods).get(callIndex);
			if(retIndex<0) return lastCall;
			lastRet=retStack().get(retIndex--);
			if(isCallPairToRet(cfg,lastCall,lastRet))
				callIndex--;
			else{
				return lastCall;
			}
		}
		return lastCall;
	}
	private List<Unit> callStack(Set<SootMethod> methods){
		List<Unit> callStack=new ArrayList<Unit>();
		for(Unit unit:path){
			if(!((Stmt)(unit)).getDefBoxes().isEmpty()&&((Stmt)(unit)).containsInvokeExpr()&&methods.contains(((Stmt)(unit)).getInvokeExpr().getMethod()))
				callStack.add(unit);
		}
		return callStack;
	}
	private List<Unit> callStack(List<SootMethod> methods){
		List<Unit> callStack=new ArrayList<Unit>();
		for(Unit unit:path){
			if(((Stmt)(unit)).containsInvokeExpr()&&!methods.contains(((Stmt)(unit)).getInvokeExpr().getMethod()))
				callStack.add(unit);
		}
		return callStack;
	}
	private List<Unit> retStack(){
		List<Unit> retStack=new ArrayList<Unit>();
		for(Unit unit:path){
			if(((Stmt)(unit)) instanceof ReturnStmt)
				retStack.add(unit);
		}
		return retStack;
	}
	public boolean isCallPairToRet(IInfoflowCFG cfg,Unit call,Unit ret){
		if(!((Stmt)(call)).containsInvokeExpr())
			return false;
		SootMethod callMethod=((Stmt)(call)).getInvokeExpr().getMethod();
		SootMethod retMethod=cfg.getMethodOf(ret);
		if(callMethod!=retMethod) return false;
		if(path.indexOf(call)>path.indexOf(ret)) return false;
		return true;	
	}
	
}
