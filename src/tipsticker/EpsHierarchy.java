package tipsticker;
/**
 * �����˼̳е�eps
 * ��ԭeps�м������ࡢimplements�е�ͬ��������eps
 * @author zxl
 *
 */
public class EpsHierarchy extends Eps {

		public EpsHierarchy(String function){
			super(function);
			eps.addAll(addSubFunctionInvoke(function));
		}
}
