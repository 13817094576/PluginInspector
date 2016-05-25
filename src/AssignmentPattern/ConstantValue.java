package AssignmentPattern;

import soot.Type;
import soot.jimple.Constant;
import soot.util.Switch;
//一个函数接受的某一个参数是constantValue是指，在某一处调用该函数的位置（unit），可以确定该参数为一个constant，在其他位置上是否为constant与之无关
public class ConstantValue extends Constant{

	@Override
	public Type getType() {
		// TODO Auto-generated method stub
		return null;
	}

	@Override
	public void apply(Switch sw) {
		// TODO Auto-generated method stub
		
	}

}
