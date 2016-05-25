package tipsticker;

public abstract class Rule {
	public int num=-1;
	public String ruleName="";
	
	public int getNum(){
		return this.num;
	};
	public void setNum(int x){
		this.num=x;
	};
	public void setRuleName(String s){
		ruleName=s;
	}
	public String getRuleName(){
		return ruleName;
	}
	
	public boolean isEmpty(){
		//ToDo
		return false;
	}
}
