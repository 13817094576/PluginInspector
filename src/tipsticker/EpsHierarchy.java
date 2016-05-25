package tipsticker;
/**
 * 考虑了继承的eps
 * 在原eps中加上子类、implements中的同名函数的eps
 * @author zxl
 *
 */
public class EpsHierarchy extends Eps {

		public EpsHierarchy(String function){
			super(function);
			eps.addAll(addSubFunctionInvoke(function));
		}
}
