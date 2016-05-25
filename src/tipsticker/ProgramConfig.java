package tipsticker;

import java.util.ArrayList;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.regex.Pattern;

import soot.FastHierarchy;
import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SootClass;
import soot.SootMethod;
import soot.Unit;
import soot.jimple.ArrayRef;
import soot.jimple.NewArrayExpr;
import soot.jimple.Stmt;
import soot.jimple.internal.JAssignStmt;
import soot.jimple.internal.JReturnStmt;
import soot.jimple.internal.JReturnVoidStmt;
import tag.IntTag;

public class ProgramConfig{
	private static List<Temporal> unsafeTemporal=Main.unsafeTemporal;
	private static List<Propagation> unsafePropagation=Main.unsafePropagation;
	private static List<Assignment> unsafeAssignment=Main.unsafeAssignment;
	private static List<String> unsafeConfiguration=Main.unsafeConfiguration;
	private static List<ConstantPropagation> unsafeConstantPropagation=Main.unsafeConstantPropagation;
	private static List<Rule> ruleAnalysis=Main.ruleAnalysis;
	
	private static Map<Integer,int[]> bindsMap=Main.bindsMap;
	
	ProgramConfig(){
	}
	
	public void printResults(){
		if(unsafeTemporal.isEmpty()){
			System.out.println("---------------unsafeTemporal is empty---------------");
		}
		else{
			System.out.println("---------------unsafeTemporal---------------Size:"+unsafeTemporal.size()+"--------------");
			int i=1;
			for(Temporal temporal:unsafeTemporal){
				System.out.println(temporal.getRuleName()+" unsafeTemporal "+i+":");
				i++;
				if(temporal.isModeThrough()){
					int index=1;
					System.out.println("Mode: PassThrough");
					for(Path path:temporal.getUnsafePaths()){
						System.out.println("\tpath "+index+":\t"+path.toString());
						index++;
					}
				}
				else if(temporal.isModeSkip()){
					int index=1;
					System.out.println("Mode: Skip");
					for(Path path:temporal.getUnsafePaths()){
						System.out.println("\tpath "+index+":\t"+path.toString());
						index++;
					}
				}
			}
		}
		if(unsafePropagation.isEmpty()){
			System.out.println("-------------------unsafePropagation is empty---------------");
		}
		else{
			System.out.println("---------------unsafePropagation---------------Size:"+unsafePropagation.size()+"----------------");
			int i=1;
			for(Propagation propagation:unsafePropagation){
				System.out.println(propagation.getRuleName()+" unsafePropagation "+i+":");
					i++;
				if(propagation.isModeMay()){	
					int index=1;
					System.out.println("Mode: May");
					for(Path path:propagation.getUnsafePaths()){
						System.out.println("\tpath "+index+":"+path.toString());
						index++;			
					}
				}
				else if(propagation.isModeMayNot()){
					System.out.println("Mode: MayNot");
					int index=1;
					for(Dp endDp:propagation.getEnd().getDps()){
						System.out.println("\tEndUnit "+index+":\t"+endDp.getEp().getUnit().toString()+" unitNum:"+endDp.getEp().getUnitNum());
						index++;
					}
				}
			}
		}
		if(unsafeAssignment.isEmpty()){
			System.out.println("-------------------unsafeAssignment is empty---------------");
		}
		else{
			System.out.println("---------------unsafeAssignment---------------Size:"+unsafeAssignment.size()+"----------------");
			for(Assignment assignment:unsafeAssignment){
				System.out.println(assignment.getRuleName()+" Dps Size:"+assignment.getDps().getDps().size());
				for(Dp dp:assignment.getDps().getDps()){
					System.out.println("\tunit:"+dp.getEp().getUnit().toString()+"\tunitNum:"+((IntTag)(dp.getEp().getUnit().getTag("unitNum"))).getIntValue());
				}
			}
		}
		if(unsafeConfiguration.isEmpty()){
			System.out.println("-------------------unsafeConfiguration is empty---------------");
		}
		else{
			System.out.println("---------------unsafeConfiguration---------------Size:"+unsafeConfiguration.size()+"----------------");
			for(String configuration:unsafeConfiguration){
				System.out.println(configuration);
			}
		}
		if(unsafeConstantPropagation.isEmpty()){
			System.out.println("-------------------unsafeConstantPropagation is empty---------------");
		}
		else{
			System.out.println("---------------unsafeConstantPropagation---------------Size:"+unsafeConstantPropagation.size()+"----------------");
			for(ConstantPropagation constantPropagation:unsafeConstantPropagation){
				System.out.println(constantPropagation.getRuleName()+" Dps Size:"+constantPropagation.getDps().getDps().size());
				for(Dp dp:constantPropagation.getDps().getDps()){
					System.out.println("\tunit:"+dp.getEp().getUnit().toString()+"\tunitNum:"+((IntTag)(dp.getEp().getUnit().getTag("unitNum"))).getIntValue());
				}
			}
		}
	}
	
	//
	// APK-scope unique ID of code unit
	// which facilitates code snippet searching
	int intTag = 0;
	
	private void inspectMethod(SootMethod m)
	{
		if(isHasBody(m)){
			Main.hasBody.add(m);
			//System.out.println("----------new body:-----------"+m.getSignature()+"-------------");	
//			System.out.println("Lcoals:"+m.getActiveBody().getLocals());
//			System.out.println("Traps:"+m.getActiveBody().getTraps());
	//	PointsToAnalysis pa=Scene.v().getPointsToAnalysis();
			
//			for(Local local:m.getActiveBody().getLocals()){
//					System.out.println("Local: "+local);
//					System.out.println(pa.reachingObjects(local));
//				}
			//if(m.hasActiveBody())
			for(Unit unit:m.getActiveBody().getUnits()){
				//add unitNum tag
				
				unit.addTag(new IntTag("unitNum",++intTag));
				
				
				//System.out.println("unit:\t"+unit+"\tunitNum:\t"+intTag);
//					if(unit instanceof JThrowStmt){
//						if(!unit.getUseBoxes().isEmpty()){
//							Value v=unit.getUseBoxes().get(0).getValue();
//							System.out.println(v.getType());
//						}
//					}
//				for(ValueBox vb:unit.getUseAndDefBoxes()){
//					if(vb.getValue() instanceof Local)
//					System.out.println(pa.reachingObjects((Local) vb.getValue()));
//				}
//					
					
//				System.out.println("unit:\t"+unit+"\t"+unit.getBoxesPointingToThis());
//				for(ValueBox vb:unit.getUseAndDefBoxes()){
//					if(vb.getValue() instanceof Local)
//						System.out.println(vb.getValue()+": "+vb.getValue().hashCode());
//				}
//					if(((Stmt)unit).containsInvokeExpr()){
//						for(Value value:((Stmt)unit).getInvokeExpr().getArgs())
//							if(value instanceof Local)
//								System.out.println(value+" "+value.hashCode());
//						//System.out.println(pa.reachingObjects((Local)value));
//					}
			//	if(unit instanceof JAssignStmt && ((JAssignStmt)unit).getLeftOp() instanceof ArrayRef){+((ArrayRef)((JAssignStmt)unit).getLeftOp()).getBase()

//					for(ValueBox vb:unit.getUseBoxes()){
//
//						if(vb.getValue() instanceof Constant)
//							System.out.println(vb+"has constant:"+vb.getValue());
//					}
//				
			//	if(((Stmt)unit).containsInvokeExpr()&&!Main.hasBody(((Stmt)unit).getInvokeExpr().getMethod()))
			//	if(unit instanceof JAssignStmt && ((JAssignStmt)unit).getRightOp() instanceof ThisRef)
				//System.out.println("unit:\t"+unit+"\tunitNum:\t"+intTag);
			
				//System.out.println(unit.getUseBoxes());
				//}
				//if(((Stmt)unit).containsArrayRef()) System.out.print("\t"+"=======");
				
                //init field map						
				if(((Stmt)(unit)).containsFieldRef()){
					if(!((Stmt)(unit)).getDefBoxes().isEmpty()){
						if(((Stmt)(unit)).getFieldRefBox()==unit.getDefBoxes().get(0)){
							if(Main.defField.keySet().contains(((Stmt)(unit)).getFieldRef().getField()))
								Main.defField.get(((Stmt)(unit)).getFieldRef().getField()).add(unit);
							else{
								List<Unit> tmp=new ArrayList<Unit>();
								tmp.add(unit);
								Main.defField.put(((Stmt)(unit)).getFieldRef().getField(),tmp);
							}
						}
						else{
							if(Main.useField.keySet().contains(((Stmt)(unit)).getFieldRef().getField()))
								Main.useField.get(((Stmt)(unit)).getFieldRef().getField()).add(unit);
							else{
								List<Unit> tmp=new ArrayList<Unit>();
								tmp.add(unit);
								Main.useField.put(((Stmt)(unit)).getFieldRef().getField(),tmp);
							}
						}
					}
				}
				// init array map 
				if(unit instanceof JAssignStmt && ((Stmt)unit).containsArrayRef()){
					if(((JAssignStmt)unit).getLeftOp() instanceof ArrayRef){
						if(Main.useArray.containsKey((((ArrayRef)(((JAssignStmt)unit).getLeftOp())).getBase()))){
							Main.useArray.get((((ArrayRef)(((JAssignStmt)unit).getLeftOp())).getBase())).add(unit);
						}
						else{
							List<Unit> ary=new ArrayList<Unit>();
							ary.add(unit);
							Main.useArray.put((((ArrayRef)(((JAssignStmt)unit).getLeftOp())).getBase()),ary);
						}
					}
					if(((JAssignStmt)unit).getRightOp() instanceof NewArrayExpr){
						if(Main.defArray.containsKey(((JAssignStmt)unit).getLeftOp()))
							Main.defArray.get(((JAssignStmt)unit).getLeftOp()).add(unit);
						else{
							List<Unit> ary=new ArrayList<Unit>();
							ary.add(unit);
							Main.defArray.put(((JAssignStmt)unit).getLeftOp(),ary);
						}
					}
				}
				
				
			}
			
		}		
	}
	
	public void programInit() {
		
		FastHierarchy hierarchy=Scene.v().getOrMakeFastHierarchy();
//		String signature="<javax.net.ssl.HostnameVerifier: boolean verify(java.lang.String,javax.net.ssl.SSLSession)>";
//		
//		for(SootClass sootClass:Scene.v().getClasses()){
			//if(sootClass.isInterface())
//			System.out.println("========="+sootClass.getName()+"================="+hierarchy.getSubclassesOf(sootClass));
//			if(sootClass.isInterface())
			
//				System.out.println(hierarchy.getAllImplementersOfInterface(sootClass));
//			else
//				System.out.println();
//			Pattern pattern=Pattern.compile(".*verify.*");
//			for(SootMethod method:sootClass.getMethods()){
//				System.out.println(method.getSignature()+"\t"+method.getDeclaringClass());
//				if(pattern.matcher(method.getSignature()).matches())
//					
//					if(method.hasActiveBody())
//					System.out.println(method.getActiveBody());
//			}
//			for(Iterator<SootMethod> iter=sootClass.methodIterator();iter.hasNext();){
//				SootMethod m = iter.next().method();
//				
//				System.out.println("----"+m.getSignature()+"-------"+m.hasActiveBody()+"-------");
//				if(m.getName().equals("onGeolocationPermissionsShowPrompt")){
//					System.out.print(false);
//				m.retrieveActiveBody();
//				System.out.print(false);
//				}
//			}
//		}
		Iterator<SootClass> classIter = Scene.v().getClasses().iterator(); 
		while (classIter.hasNext()) 
		{
			SootClass curClass = classIter.next();
			
			//
			// Traverse each method in current class
			Iterator<SootMethod> methodIter = curClass.getMethods().iterator();
			while (methodIter.hasNext())
			{
				//		System.out.println("------"+m.getSignature()+"---------");
				inspectMethod(methodIter.next());
			}
		}
	}
// a method hasbody means it has a ret unit
	private static boolean isHasBody(SootMethod m){
		if(!m.hasActiveBody()&&m.isConcrete()) m.retrieveActiveBody();
		if(m.hasActiveBody()){
			for(Unit unit:m.getActiveBody().getUnits()){
				if(((Stmt)(unit))instanceof JReturnStmt||((Stmt)(unit))instanceof JReturnVoidStmt)
					return true;
			}
		}
		return false;
	}
}
