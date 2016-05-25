package tipsticker;

import soot.jimple.Stmt;
/**
 * 考虑了继承的dps
 * 在原dps中加上子类、implemnts中的同名函数的dps
 * @author zxl
 *
 */
public class DpsHierarchy extends Dps {

	public DpsHierarchy(String function,int argNum){
		Eps tmpeps=new EpsHierarchy(function);
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
	public DpsHierarchy(String field){
		super(field);
	}
}

