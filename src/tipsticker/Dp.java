package tipsticker;

import soot.Unit;
import soot.Value;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JIdentityStmt;
import soot.jimple.internal.JStaticInvokeExpr;

/**
 * 
 * @author zxl
 * a dp is a data point. it has some forms including method-call,field currently. other forms may be extended sometimes.
 * 
 *some Dp examples:
 *dps=Arg("android.cotent.Context.openOrCreatDatabase",2);
 *dps=Ret("android.cotent.Context.openOrCreatDatabase")
 */
public class Dp {
	private Ep ep;
//argNum points out the critical-param we should cared.0 is this;1 is the first param;2 is the second param.....
	private int argNum;
	
	public Dp(Ep e,int value){
		this.ep=e;
		this.argNum=value;
	}
	public Dp(Unit e,int value){
		this.ep=new Ep(e);
		this.argNum=value;
	}
	public Ep getEp(){
		return this.ep;
	}
	public int getArgNum(){
		return this.argNum;
	}
	public void setArgNum(int n){
		argNum=n;
	}
	public boolean isEqual(Dp dp){
		return this.ep.isEqual(dp.getEp())&&this.argNum==dp.getArgNum();
	}
	
	public Value getValue(){
		Value v=null;
		Unit s=ep.getUnit();
		if(argNum==-1){
			if(s instanceof JAssignStmt || s instanceof JIdentityStmt)
				v=s.getDefBoxes().get(0).getValue();
		}
		else if(argNum==0){
			if(((Stmt)s).containsInvokeExpr() && !(((Stmt)s).getInvokeExpr() instanceof JStaticInvokeExpr))
				v=s.getUseBoxes().get(0).getValue();
		}
		else if(argNum>=1){
			if(((Stmt)s).containsInvokeExpr() && !(((Stmt)s).getInvokeExpr() instanceof JStaticInvokeExpr))
				v=s.getUseBoxes().get(argNum).getValue();
			else 
				v=s.getUseBoxes().get(argNum-1).getValue();
		}
		return v;
	}
}
