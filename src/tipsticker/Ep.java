package tipsticker;

import soot.Unit;
import tag.IntTag;
import soot.jimple.Stmt;
import tag.StringTag;
/**
 *  @author zxl
 *a ep is a execute point.commonly,it represents a method-call unit without considering its params.
 *some Ep examples:
 *eps1=FunctionInvoke("android.cotent.Context.openOrCreatDatabase");
 *
 */

public class Ep {
	private Unit ep;
	private int unitNum;
	
	private boolean isENTRY=false;
	private boolean isEXIT=false;
	
	private Ep predecessor=null;
	private Ep successor=null;
	
	
	public Ep(Unit ep){
		this.ep=ep;	
		this.unitNum=((IntTag)(ep.getTag("unitNum"))).getIntValue();
	}
	public Ep getPredecessor(){
		return this.predecessor;
	}
	public Ep getSuccessor(){
		return this.successor;
	}
	public void setPredecessor(Ep e){
		this.predecessor=e;
	}
	public void setSuccessor(Ep e){
		this.successor=e;
	}
	public boolean ishasPredecesor(){
		if(this.predecessor==null)
			return false;
		return true;
	}
	public boolean ishasSuccessor(){
		if(this.successor==null)
			return false;
		return true;
	}
	public Unit getUnit(){
		return this.ep;
	}
	public int getUnitNum(){
		this.unitNum=((IntTag)(ep.getTag("unitNum"))).getIntValue();
		return this.unitNum;
	}
	public void setUnitNum(int value){
		this.unitNum=value;
	}
	
	public void setENTRY(){
		this.isENTRY=true;
		this.isEXIT=false;
	}
	public void setEXIT(){
		this.isEXIT=true;
		this.isENTRY=false;
	}
	public boolean isENTRY(){
		return isENTRY;
	}
	public boolean isEXIT(){
		return isEXIT;
	}
	
	public boolean isEqual(Ep ep){
		boolean set=true;
		if(this.getUnitNum()!=ep.getUnitNum()) set=false;
		return set;
	}
	
	public String toString(){
		return "unit:"+this.ep.toString()+"\tunitNum:"+this.unitNum;
	}
}
