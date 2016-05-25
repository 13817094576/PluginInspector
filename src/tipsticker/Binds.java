package tipsticker;

import java.util.ArrayList;
import java.util.List;
/**
 * binds(dps1,dps2)可以将dps1和dps2绑定在一起，在processAllAnalysis（）之后，使dps1和dps2被重新赋值为dps1和dps2的交集
 * binds的目的是为了使某一dps可以满足多条Rule
 * 被绑定在一起的dps，拥有相同的DPS_AND_EPS_NUM
 * eps和dps一样适用于binds()函数
 * @author zxl
 *
 */
public class Binds extends Rule{
	
	Binds(){
	}
	Binds(Object v1,Object v2){
		if((v1 instanceof Dps)&&(v2 instanceof Dps)){
			Binds1((Dps)v1,(Dps)v2);
		}
		else if((v1 instanceof Dps)&&(v2 instanceof Eps)){
			Binds2((Dps)v1,(Eps)v2);
		}
		else if((v1 instanceof Eps)&&(v2 instanceof Eps)){
			Binds3((Eps)v1,(Eps)v2);
		}
	}
	
	private void Binds1(Dps dps1,Dps dps2){
		if(dps1.getNum()==-1){
			if(dps2.getNum()==-1){
				++Main.DPS_AND_EPS_NUM;
				dps1.setNum(Main.DPS_AND_EPS_NUM);
				dps2.setNum(Main.DPS_AND_EPS_NUM);
			}
			else
				dps1.setNum(dps2.getNum());
		}
		else
			dps2.setNum(dps1.getNum());	
		getBinded(dps1,dps2);
	}
	private void Binds2(Dps dps,Eps eps){
		if(dps.getNum()==-1){
			if(eps.getNum()==-1){
				++Main.DPS_AND_EPS_NUM;
				dps.setNum(Main.DPS_AND_EPS_NUM);
				eps.setNum(Main.DPS_AND_EPS_NUM);
			}
			else
				dps.setNum(eps.getNum());
		}
		else
			eps.setNum(dps.getNum());
		
		getBinded(dps,eps);	
	}
	private void Binds3(Eps eps1,Eps eps2){
		if(eps1.getNum()==-1){
			if(eps2.getNum()==-1){
				++Main.DPS_AND_EPS_NUM;
				eps1.setNum(Main.DPS_AND_EPS_NUM);
				eps2.setNum(Main.DPS_AND_EPS_NUM);
			}
			else
				eps1.setNum(eps2.getNum());
		}
		else
			eps2.setNum(eps1.getNum());
		getBinded(eps1,eps2);
	}
	/**
	 * tobind(v1,v2)会查找v1和v2中被绑定在一起的dps或eps并取交集
	 * 
	 * @param v1
	 * @param v2
	 * @return
	 */
	public boolean toBind(Object v1,Object v2){
		if((v1 instanceof Dps)&&(v2 instanceof Dps)){
			return getBinded((Dps)v1,(Dps)v2);
		}
		else if((v1 instanceof Dps)&&(v2 instanceof Eps)){
			return getBinded((Dps)v1,(Eps)v2);
		}
		else if((v1 instanceof Eps)&&(v2 instanceof Eps)){
			return getBinded((Eps)v1,(Eps)v2);
		}
		else if((v1 instanceof Assignment)&&(v2 instanceof Assignment)){
			return getBinded((Assignment)v1,(Assignment)v2);
		}
		else if((v1 instanceof Assignment)&&(v2 instanceof Propagation)){
			return getBinded((Assignment)v1,(Propagation)v2);
		}
		else if((v1 instanceof Assignment)&&(v2 instanceof Temporal)){
			return getBinded((Assignment)v1,(Temporal)v2);
		}
		else if((v1 instanceof Propagation)&&(v2 instanceof Propagation)){
			return getBinded((Propagation)v1,(Propagation)v2);
		}
		else if((v1 instanceof Propagation)&&(v2 instanceof Temporal)){
			return getBinded((Propagation)v1,(Temporal)v2);
		}
		else if((v1 instanceof Temporal)&&(v2 instanceof Temporal)){
			return getBinded((Temporal)v1,(Temporal)v2);
		}
		return false;
	}
	/**
	 * 类似于伪代码：
	 * 	dps1=dps1 ∩ dps2
	 *  dps2=dps1
	 * @param dps1
	 * @param dps2
	 * @return 若dsp1和dps2有不同的unit，则返回true，即返回dps1或dps2是否被修改
	 */
	private  boolean getBinded(Dps dps1,Dps dps2){
		boolean set=false;
		Dps tmp1=new Dps(dps1.getDps());
		Dps tmp2=new Dps(dps2.getDps());
		dps1.getDps().clear();
		dps2.getDps().clear();
		for(Dp dp:tmp1.getDps()){
			if(tmp2.contains(dp.getEp().getUnit())){
				dps1.getDps().add(dp);
				dps2.getDps().add(dp);
			}
			else set=true;
		}
		for(Dp dp:tmp2.getDps()){
			if(tmp1.contains(dp.getEp().getUnit())){
				if(!dps1.contains(dp.getEp().getUnit())){
					dps1.getDps().add(dp);
					dps2.getDps().add(dp);
				}
			}
			else set=true;
		}
		return set;
	}
	/**
	 * 类似于伪代码：
	 * 	dps=dps ∩ eps
	 * 	eps=dps ∩ eps
	 * @param dps
	 * @param eps
	 * @return 若dps和eps有不同的unit，则返回true，即返回dps或eps是否被修改
	 */
	private  boolean getBinded(Dps dps,Eps eps){
		boolean set=false;
		Dps tmp1=new Dps(dps.getDps());
		Eps tmp2=new Eps(eps.getEps());
		dps.getDps().clear();
		eps.getEps().clear();
		for(Dp dp:tmp1.getDps()){
			if(tmp2.contains(dp.getEp().getUnit())){
				dps.getDps().add(dp);
				eps.getEps().add(dp.getEp());
			}
			else set=true;
		}
		for(Ep ep:tmp2.getEps()){
			boolean flag=false;
			for(Dp dp:tmp1.getDps()){
				if(dp.getEp().isEqual(ep)){
					flag=true;
					dps.getDps().add(dp);
					eps.getEps().add(ep);
				}
			}
			if(!flag) set=true;
		}
		return set;
	}
	/**
	 * 类似于伪代码：
	 * 	eps1=eps1 ∩ eps2
	 * 	eps2=eps1
	 * @param eps1
	 * @param eps2
	 * @return 若eps1和eps2有不同的unit则返回true，即返回eps1或eps2是否被修改
	 */
	private  boolean getBinded(Eps eps1,Eps eps2){
		boolean set=false;
		List<Ep> tmp1=new ArrayList<Ep>();
		List<Ep> tmp2=new ArrayList<Ep>();
		tmp1.addAll(eps1.getEps());
		tmp2.addAll(eps2.getEps());
		eps1.getEps().clear();
		eps2.getEps().clear();
		for(Ep ep:tmp1){
			if(tmp2.contains(ep.getUnit())){
				eps1.getEps().add(ep);
				eps2.getEps().add(ep);
			}
			else
				set=true;
		}
		for(Ep ep:tmp1){
			if(tmp2.contains(ep.getUnit())){
				if(!eps1.contains(ep.getUnit())){
					eps1.getEps().add(ep);
					eps2.getEps().add(ep);
				}
			}
			else
				set=true;
		}
		return set;
	}
	/**
	 * 判断assg1的dps和assg2的是否拥有相同的DPS_AND_EPS_NUM
	 * 若相同，则对它们取交集
	 * @param assg1
	 * @param assg2
	 * @return 返回assg1或assgn2是否被修改
	 */
	private  boolean getBinded(Assignment assg1,Assignment assg2){
		if(assg1.getDps().getNum()==-1||assg2.getDps().getNum()==-1||assg1.getDps().getNum()!=assg2.getDps().getNum())
			return false;
		return getBinded(assg1.getDps(),assg2.getDps());
	}
	/**
	 * 判断assgn的dps是否和propa的2个dps拥有相同DPS_AND_EPS_NUM
	 * 若相同，则对它们取交集
	 * @param assgn
	 * @param propa
	 * @return 返回assgn或propa是否被修改
	 */
	private  boolean getBinded(Assignment assgn,Propagation propa){
		boolean flag=false;
		if(assgn.getDps().getNum()==-1)
			return false;
		if(propa.getStart().getNum()!=assgn.getDps().getNum()){
			if(propa.getEnd().getNum()!=assgn.getDps().getNum())
				return false;
			else{
				flag=getBinded(assgn.getDps(),propa.getEnd());
				propa.pathAndDps();
			}
		}
		else{
			flag=getBinded(assgn.getDps(),propa.getStart());
			propa.pathAndDps();//修改了propa的dps后，可能会失去一些dp，依赖这些dp的path应该被删掉
		}
		return flag;
	}
	//
	//下面几个getBinded（）函数，类似于之前的
	//
	private  boolean getBinded(Assignment assgn,Temporal temporal){
		boolean flag=false;
		if(assgn.getDps().getNum()==-1)
			return flag;
		if(assgn.getDps().getNum()==temporal.getStart().getNum()){
			flag=getBinded(assgn.getDps(),temporal.getStart());
		}
		if(assgn.getDps().getNum()==temporal.getPass().getNum()){
			flag=getBinded(assgn.getDps(),temporal.getPass());
		}
		if(assgn.getDps().getNum()==temporal.getEnd().getNum()){
			flag=getBinded(assgn.getDps(),temporal.getEnd());
		}
		temporal.pathAndEps();
		return flag;
	}
	private  boolean getBinded(Propagation propa,Propagation propb){
		boolean flag=false;
		if(propa.getStart().getNum()==propb.getEnd().getNum()){
			if(propa.getStart().getNum()==-1)
				return flag;
			flag=getBinded(propa.getStart(),propb.getEnd());			
		}
		if(propa.getEnd().getNum()==propb.getStart().getNum()){
			if(propa.getEnd().getNum()==-1)
				return flag;
			flag=getBinded(propa.getEnd(),propb.getStart());
		}
		propa.pathAndDps();
		propb.pathAndDps();
		return flag;
	}
	private  boolean getBinded(Propagation propa, Temporal temporal){
		boolean flag=false;
		if(propa.getStart().getNum()==temporal.getStart().getNum()&&propa.getStart().getNum()!=-1){
			flag=getBinded(propa.getStart(),temporal.getStart());
		}
		if(propa.getStart().getNum()==temporal.getPass().getNum()&&propa.getStart().getNum()!=-1){
			flag=getBinded(propa.getStart(),temporal.getPass());
		}
		if(propa.getStart().getNum()==temporal.getEnd().getNum()&&propa.getStart().getNum()!=-1){
			flag=getBinded(propa.getStart(),temporal.getEnd());
		}
		if(propa.getEnd().getNum()==temporal.getStart().getNum()&&propa.getEnd().getNum()!=-1){
			flag=getBinded(propa.getEnd(),temporal.getStart());
		}
		if(propa.getEnd().getNum()==temporal.getPass().getNum()&&propa.getEnd().getNum()!=-1){
			flag=getBinded(propa.getEnd(),temporal.getPass());
		}
		if(propa.getEnd().getNum()==temporal.getEnd().getNum()&&propa.getEnd().getNum()!=-1){
			flag=getBinded(propa.getEnd(),temporal.getEnd());
		}
		propa.pathAndDps();
		temporal.pathAndEps();
		return flag;
	}
	private  boolean getBinded(Temporal temporal1,Temporal temporal2){
		boolean flag=false;
		if(temporal1.getStart().getNum()==temporal2.getStart().getNum()&&temporal1.getStart().getNum()!=-1){
			flag=getBinded(temporal1.getStart(),temporal2.getStart());
		}
		if(temporal1.getStart().getNum()==temporal2.getPass().getNum()&&temporal1.getStart().getNum()!=-1){
			flag=getBinded(temporal1.getStart(),temporal2.getPass());
		}
		if(temporal1.getStart().getNum()==temporal2.getEnd().getNum()&&temporal1.getStart().getNum()!=-1){
			flag=getBinded(temporal1.getStart(),temporal2.getEnd());
		}
		if(temporal1.getPass().getNum()==temporal2.getStart().getNum()&&temporal1.getPass().getNum()!=-1){
			flag=getBinded(temporal1.getPass(),temporal2.getStart());
		}
		if(temporal1.getPass().getNum()==temporal2.getPass().getNum()&&temporal1.getPass().getNum()!=-1){
			flag=getBinded(temporal1.getPass(),temporal2.getPass());
		}
		if(temporal1.getPass().getNum()==temporal2.getEnd().getNum()&&temporal1.getPass().getNum()!=-1){
			flag=getBinded(temporal1.getPass(),temporal2.getEnd());
		}
		if(temporal1.getEnd().getNum()==temporal2.getStart().getNum()&&temporal1.getEnd().getNum()!=-1){
			flag=getBinded(temporal1.getEnd(),temporal2.getStart());
		}
		if(temporal1.getEnd().getNum()==temporal2.getPass().getNum()&&temporal1.getEnd().getNum()!=-1){
			flag=getBinded(temporal1.getEnd(),temporal2.getPass());
		}
		if(temporal1.getEnd().getNum()==temporal2.getEnd().getNum()&&temporal1.getEnd().getNum()!=-1){
			flag=getBinded(temporal1.getEnd(),temporal2.getEnd());
		}
		temporal1.pathAndEps();
		temporal2.pathAndEps();
		return flag;
	}
}
