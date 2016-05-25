package tipsticker;

import java.io.BufferedReader;
import java.io.File;
import java.io.FileNotFoundException;
import java.io.FileReader;
import java.io.IOException;
import java.util.ArrayList;
import java.util.HashMap;
import java.util.HashSet;
import java.util.Iterator;
import java.util.List;
import java.util.Map;
import java.util.Set;
import java.util.TreeSet;

import soot.MethodOrMethodContext;
import soot.Scene;
import soot.SootClass;
import soot.SootField;
import soot.SootMethod;
import soot.Unit;
import soot.UnitBox;
import soot.Value;
import soot.jimple.infoflow.IInfoflow.CallgraphAlgorithm;
import soot.jimple.infoflow.InfoflowResults;
import soot.jimple.infoflow.android.AndroidSourceSinkManager.LayoutMatchingMode;
import soot.jimple.infoflow.android.IMethodSpec;
import soot.jimple.infoflow.android.SetupApplication;
import soot.jimple.infoflow.android.data.AndroidMethod;
import soot.jimple.infoflow.solver.IInfoflowCFG;
import soot.jimple.infoflow.taintWrappers.EasyTaintWrapper;
import soot.options.Options;
import AssignmentPattern.Both;
import AssignmentPattern.ConstantValue;
import AssignmentPattern.Match;
import AssignmentPattern.Not;
import AssignmentPattern.OneOf;
import AssignmentPattern.Range;
import AssignmentPattern.StaticValue;
import ConfigurationPattern.ExceptionContain;
import ConfigurationPattern.MethodContain;
import ConfigurationPattern.ReturnContain;

public class Main {
	//Output option
	public static boolean OneSorceOnePath=true;//only find one path in propagation() for a Sorce and then return
	
	//Analysis option
	public static int CallPathMaxLength=100;
	
	//Input option for soot
	public static boolean withPath = false;
	public static String androidJar, apkFile, taintFile;
	
	public static SetupApplication app;
	public static IInfoflowCFG cfg;
	
	//int-number used for adding tags
	public static int DPS_AND_EPS_NUM=0;
	public static int RULE_NUM=0;
	
	protected static String ENTRY="ENTRY";
	protected static String EXIT="EXIT";
	protected static String PROP_MUST="must";
	protected static String PROP_MAY="prop_may";
	protected static String PROP_MAYNOT="prop_maynot";
	protected static String PROP_PASS_THROUGH="prop_pass_through";
	protected static String PROP_SKIP="prop_skip";
	protected static StaticValue StaticValue=new StaticValue();//constant & equality
	protected static ConstantValue ConstantValue=new ConstantValue();//constant & no equality
	protected String UnsafeMethodCall="unsafeMethodCall";
	protected static String Hierarchy="hierarchy";
	
	//unsafe code found in process all analysis
	public static List<Temporal> unsafeTemporal=new ArrayList<Temporal>();
	public static List<Propagation> unsafePropagation=new ArrayList<Propagation>();
	public static List<Assignment> unsafeAssignment=new ArrayList<Assignment>();
	public static List<String> unsafeConfiguration=new ArrayList<String>();
	public static List<ConstantPropagation> unsafeConstantPropagation=new ArrayList<ConstantPropagation>();
	
	// rules defined in readrules()
	public static List<Rule> ruleAnalysis=new ArrayList<Rule>();
	
	public static Map<Integer,int[]> bindsMap=new HashMap<Integer,int[]>();
	public static List<SootMethod> hasBody=new ArrayList<SootMethod>();
	public static Map<SootField,List<Unit>> defField=new HashMap<SootField,List<Unit>>();
	public static Map<SootField,List<Unit>> useField=new HashMap<SootField,List<Unit>>();
	public static Map<Value,List<Unit>> defArray=new HashMap<Value,List<Unit>>();
	public static Map<Value,List<Unit>> useArray=new HashMap<Value,List<Unit>>();

	//
	// Exit status
	private final static int EXIT_STATUS_NORMAL = 0;
	private final static int EXIT_STATUS_ERROR = 1;
	
	public static void main(String[] args) throws IOException {
		for (int i = 0; i < args.length; i++) {
			if (args[i].equals("--android-jar")) {
				i++;
				androidJar = args[i];
			}
			else if (args[i].equals("--with-path")) {
				withPath = true;
			}
			else if (args[i].endsWith(".apk")) {
				apkFile = args[i];
			}
			else if (args[i].endsWith(".taint"))
			{
				taintFile = args[i];
			}
		}
		
		//
		// Check parameters
		
		// Check if APK file exists
		File apkFileInstance = new File(apkFile);
		if (!apkFileInstance.exists())
		{
			System.err.println("Error: APK File doesn't exist, " + apkFile);
			System.exit(EXIT_STATUS_ERROR);
		}
			
		try{
			final long beforeRun = System.nanoTime();
			app = new SetupApplication(androidJar, apkFile);
			app.setStopAfterFirstFlow(false);
			app.setEnableImplicitFlows(false);
			app.setEnableStaticFieldTracking(true);
			app.setEnableCallbacks(true);
			app.setEnableExceptionTracking(true);
			app.setAccessPathLength(1);
			app.setLayoutMatchingMode(LayoutMatchingMode.NoMatch);
			app.setFlowSensitiveAliasing(true);
			app.setComputeResultPaths(withPath);
			app.setCallgraphAlgorithm(CallgraphAlgorithm.AutomaticSelection);
			app.setTaintWrapper(new EasyTaintWrapper("EasyTaintWrapperSource.txt"));
			

			
			calculateSourcesSinksEntrypoints();
			InfoflowResults results = app.runInfoflow();
			
			cfg=app.getCFG();
		//	new SSL_v1_include_DeadCode();
			programInit();
			readRules();
			process();
			printResults();
			
			final long finalRun=System.nanoTime();
			System.out.println("analysis time:"+(finalRun-beforeRun)/1000000000 + "seconds");
		}
		catch (RuntimeException ex) {
			System.err.println("Exception occurred: " + ex.getMessage());
			ex.printStackTrace();
		}
	}
	
//write your rules here.
	public static void readRules(){
//for example:
//		Dps dps1=Ret("<com.example.externalstorage.localImplements: boolean verify()>");
//		Dps dps2=Ret("<com.example.externalstorage.localInterface: boolean verify()>");
//		
//		Dps dps3=RetHierarchy("<com.example.externalstorage.localImplements: boolean verify()>");
//	    Dps dps4=RetHierarchy("<com.example.externalstorage.localInterface: boolean verify()>");
//		Dps dps1=Arg("<com.example.externalstorage.MainActivity: void print(java.lang.String)>",1);
//		Rule r1=Assignment(dps1,StaticValue);
//		Detect(r1);
		
//		Dps dps1=Ret("android.content.Intent.setClass");
//		Dps dps2=Arg("android.app.PendingIntent.getActivity",3);
//		Rule r1=Propagation(dps1,dps2,PROP_MAY);
//		Detect(r1);
		
		// EditText.getText
		Dps dpsGetText = ArgHierarchy("android.widget.EditText.getText", 0);
		Dps dpsText = Ret("android.widget.EditText.getText");
		Binds(dpsGetText, dpsText);
		
		// HTTP communication
		Dps dpsHttpPost = Arg("org.apache.http.client.methods.HttpPost.<init>", 1);
		Rule ruleHttpPost = Propagation(dpsText, dpsHttpPost, PROP_MAY);
		
		Dps dpsHttpGet = Arg("org.apache.http.client.methods.HttpGet.<init>", 1);
		Rule ruleHttpGet = Propagation(dpsText, dpsHttpGet, PROP_MAY);
		
		Dps dpsHttpPut = Arg("org.apache.http.client.methods.HttpPut.<init>", 1);
		Rule ruleHttpPut = Propagation(dpsText, dpsHttpPut, PROP_MAY);
		
		Dps dpsOutputStream = ArgHierarchy("java.io.OutputStream.write", 1);
		Rule ruleOutputStream = Propagation(dpsText, dpsOutputStream, PROP_MAY);
		
		Dps dpsOutputStreamWriter = ArgHierarchy("java.io.OutputStreamWriter.write", 1);
		Rule ruleOutputStreamWriter = Propagation(dpsText, dpsOutputStreamWriter, PROP_MAY);
		
		Dps dpsBufferedWriter = ArgHierarchy("java.io.BufferedWriter.write", 1);
		Rule ruleBufferedWriter = Propagation(dpsText, dpsBufferedWriter, PROP_MAY);
		
		Dps dpsUrl = Arg("java.net.URL.<init>", 1);
		Rule ruleUrl = Propagation(dpsText, dpsUrl, PROP_MAY);
		
		Dps dpsUri = Arg("java.net.URI.<init>", 1);
		Rule ruleUri = Propagation(dpsText, dpsUri, PROP_MAY);
		
		Dps dpsCredentialsArg1 = Arg("org.apache.http.auth.UsernamePasswordCredentials.<init>", 1);
		Rule ruleCredentialsArg1 = Propagation(dpsText, dpsCredentialsArg1, PROP_MAY);
		
		Dps dpsCredentialsArg2 = Arg("org.apache.http.auth.UsernamePasswordCredentials.<init>", 2);
		Rule ruleCredentialsArg2 = Propagation(dpsText, dpsCredentialsArg2, PROP_MAY);
		
		Rule[] rules = { ruleHttpPost, ruleHttpGet, ruleHttpPut, 
						 ruleOutputStream, ruleOutputStreamWriter, ruleBufferedWriter,
						 ruleUrl, ruleUri,
						 ruleCredentialsArg1, ruleCredentialsArg2 };
		Detect(rules);
	}
	
	private static void calculateSourcesSinksEntrypoints() throws IOException {
		Set<AndroidMethod> sources = new HashSet<AndroidMethod>();
		Set<AndroidMethod> sinks = new HashSet<AndroidMethod>();
		app.calculateSourcesSinksEntrypoints(sources, sinks, new HashSet<IMethodSpec>());
	}
	
	
	
// execution points
	public static Eps FunctionInvoke(String function){
		return new Eps(function);
	}
	public static Eps FunctionInvokeHierarchy(String function){
		return new EpsHierarchy(function);
	}
	public static Eps New_Eps(String expr){
		return new Eps(expr,"NewExpr");
	}
//data points	
	public static Dps Arg(String function,int argNum){
		return new Dps(function,argNum);
	}
	public static Dps Ret(String function){
		return Arg(function,-1);
	}
	public static Dps Return(String function){
		return Arg(function,-1);
	}
	public static Dps New(String expr){
		return new Dps(expr,"NewExpr");
	}
	public static Dps Field(String field){
		return new Dps(field);
	}
	public static Dps ArgHierarchy(String function,int argNum){
		return new DpsHierarchy(function,argNum);
	}
	public static Dps RetHierarchy(String function){
		return new DpsHierarchy(function,-1);
	}
	public static Dps ReturnHierarchy(String function){
		return new DpsHierarchy(function,-1);
	}
//rule:configuration
	public static Configuration MethodConfiguration(String signature,Object pattern){
		return new MethodConfiguration(signature,pattern);
	}
	public static Configuration MethodConfiguration(String signature,Object pattern,String hierarchy){
		return new MethodConfiguration(signature,pattern,hierarchy);
	}
	public static ExceptionContain ExceptionContain(Exception e){
		return new ExceptionContain(e);
	}
	public static ReturnContain ReturnContain(boolean v){
		return new ReturnContain(v);
	}
	public static ReturnContain ReturnContain(boolean v,String mode){
		return new ReturnContain(v,mode);
	}
	public static MethodContain MethodContain(String s){
		return new MethodContain(s);
	}
//rule:Assignment r=Assignment(dps,pattern);
	public static Assignment Assignment(Dps dps1,Object v){
		return new Assignment(dps1,v);
	}
	public static OneOf OneOf(Object v1,Object v2){
		return new OneOf(v1,v2);
	}
	public static OneOf OneOf(int[] list){
		return new OneOf(list);
	}
	public static Match Match(String str){
		return new Match(str);
	}
	public static Range Range(String str){
		return new Range(str);
	}
	public static Not Not(Object v){
		return new Not(v);
	}
	public static Both Both(Object v1,Object v2){
		return new Both(v1,v2);
	}
//rule:Propagation r=Propagation(dps1,dps2,mode);
	public static Propagation Propagation(Dps dps1,Dps dps2,String mode){
		return new Propagation(dps1,dps2,mode);
	}
	
//rule:Temporal: t=Temporal(eps1,eps2,eps3,mode);
	public static Temporal Temporal(Eps eps1,Eps eps2,Eps eps3,String mode){
		return new Temporal(eps1,eps2,eps3,mode);
	}
//and
	public static void And(Rule r1,Rule r2){
		if(r1.isEmpty()||r2.isEmpty()){
			ruleAnalysis.remove(r1);
			ruleAnalysis.remove(r2);
			return;
		}
		if(r1.getNum()!=-1){
			r2.setNum(r1.getNum());
			return;
		}
		if(r2.getNum()!=-1){
			r1.setNum(r2.getNum());
			return;
		}
		RULE_NUM++;
		r1.setNum(RULE_NUM);
		r2.setNum(RULE_NUM);
	}
//binds
	public static void Binds(Object v1,Object v2){
		new Binds(v1,v2);
	}
	public static boolean getBinded(Object v1,Object v2){
		return new Binds().toBind(v1, v2);
	}
	
	
//detect
	public static void Detect(Rule r[]){
		for(int i=0;i<r.length;i++)
			ruleAnalysis.add(r[i]);
	}
	public static void Detect(Rule r1){
		ruleAnalysis.add(r1);
	}
	public static void Detect(Rule r1,Rule r2){
		ruleAnalysis.add(r1);
		ruleAnalysis.add(r2);
	}
	public static void Detect(Rule r1,Rule r2,Rule r3){
		ruleAnalysis.add(r1);
		ruleAnalysis.add(r2);
		ruleAnalysis.add(r3);
	}
	public static void Detect(Rule r1,Rule r2,Rule r3,Rule r4){
		ruleAnalysis.add(r1);
		ruleAnalysis.add(r2);
		ruleAnalysis.add(r3);
		ruleAnalysis.add(r4);
	}
	public static void Detect(Rule r1,Rule r2,Rule r3,Rule r4,Rule r5){
		ruleAnalysis.add(r1);
		ruleAnalysis.add(r2);
		ruleAnalysis.add(r3);
		ruleAnalysis.add(r4);
		ruleAnalysis.add(r5);
	}
	public static void Detect(Rule r1,Rule r2,Rule r3,Rule r4,Rule r5,Rule r6,Rule r7,Rule r8){
		ruleAnalysis.add(r8);
		ruleAnalysis.add(r7);
		ruleAnalysis.add(r6);
		ruleAnalysis.add(r5);
		ruleAnalysis.add(r4);
		ruleAnalysis.add(r3);
		ruleAnalysis.add(r2);
		ruleAnalysis.add(r1);
	}
	
//processResults
	public static void process(){
		processAllAnalysis();
		processBindsInResults();
//		processAndInResults();
		processEmptyListInResults();
	}
	public static void processBindsInResults(){
		boolean set=false;
		while(!set){
			set=true;
			for(Assignment assignment:unsafeAssignment){
				List<Assignment> tmpList=new ArrayList<Assignment>();
				tmpList.addAll(unsafeAssignment);
				tmpList.remove(assignment);	
				for(Assignment tmpAssignment:tmpList){
					if(getBinded(tmpAssignment,assignment))
						set=false;
				}
				for(Propagation propagation:unsafePropagation){
					if(getBinded(assignment,propagation))
						set=false;
				}
				for(Temporal temporal:unsafeTemporal){
					if(getBinded(assignment,temporal))
						set=false;
				}
			}
			for(Propagation propagation:unsafePropagation){
				List<Propagation> tmpList=new ArrayList<Propagation>();
				tmpList.addAll(unsafePropagation);
				tmpList.remove(propagation);
				for(Propagation tmpPropagation:tmpList){
					if(getBinded(tmpPropagation,propagation))
						set=false;
				}
				for(Temporal temporal:unsafeTemporal){
					if(getBinded(propagation,temporal))
						set=false;
				}
			}
			for(Temporal temporal:unsafeTemporal){
				List<Temporal> tmpList=new ArrayList<Temporal>();
				tmpList.addAll(unsafeTemporal);
				tmpList.remove(temporal);
				for(Temporal tmpTemporal:tmpList){
					if(getBinded(temporal,tmpTemporal))
						set=false;
				}
			}
		}
	}
	public static void processAndInResults(){
		if(!unsafeAssignment.isEmpty()){
			for(Assignment assignment:unsafeAssignment){
				if(assignment.getNum()!=-1){
					List<Assignment> tmpList=new ArrayList<Assignment>();
					tmpList.addAll(unsafeAssignment);
					tmpList.remove(assignment);
					for(Assignment tmpAssignment:tmpList){
						if(tmpAssignment.getNum()==assignment.getNum()){
							if(tmpAssignment.isEmpty()||assignment.isEmpty()){
								tmpAssignment.clear();
								assignment.clear();
							}
						}
					}
					for(Propagation propagation:unsafePropagation){
						if(propagation.getNum()==assignment.getNum()){
							if(propagation.isEmpty()||assignment.isEmpty()){
								propagation.clear();
								assignment.clear();;
								
							}
						}
					}
					for(Temporal temporal:unsafeTemporal){
						if(temporal.getNum()==assignment.getNum()){
							if(assignment.isEmpty()||temporal.isEmpty()){
								assignment.clear();
								temporal.clear();
							}
						}
					}
				}
			}
		}
		if(!unsafePropagation.isEmpty()){
			for(Propagation propagation:unsafePropagation){
				if(propagation.getNum()!=-1){
					for(Assignment assignment:unsafeAssignment){
						if(propagation.getNum()==assignment.getNum()){
							if(propagation.isEmpty()||assignment.isEmpty()){
								assignment.clear();
								propagation.clear();
							}
						}
					}
					List<Propagation> tmpList=new ArrayList<Propagation>();
					tmpList.addAll(unsafePropagation);
					tmpList.remove(propagation);
					for(Propagation tmpPropagation:tmpList){
						if(propagation.getNum()==tmpPropagation.getNum()){
							if(propagation.isEmpty()||tmpPropagation.isEmpty()){
								propagation.clear();;
								tmpPropagation.clear();
							}
						}
					}
					for(Temporal temporal:unsafeTemporal){
						if(propagation.getNum()==temporal.getNum()){
							if(propagation.isEmpty()||temporal.isEmpty()){
								propagation.clear();
								temporal.clear();
							}
						}
					}
				}
			}
		}
		if(!unsafeTemporal.isEmpty()){
			for(Temporal temporal:unsafeTemporal){
				if(temporal.getNum()!=-1){
					for(Assignment assignment:unsafeAssignment){
						if(assignment.getNum()==temporal.getNum()){
							if(assignment.isEmpty()||temporal.isEmpty()){
								assignment.clear();
								temporal.clear();
							}
						}
					}
					for(Propagation propagation:unsafePropagation){
						if(propagation.getNum()==temporal.getNum()){
							if(propagation.isEmpty()||temporal.isEmpty()){
								propagation.clear();
								temporal.clear();
							}
						}
					}
					List<Temporal> tmpList=new ArrayList<Temporal>();
					tmpList.addAll(unsafeTemporal);
					tmpList.remove(temporal);
					for(Temporal tmpTemporal:tmpList){
						if(temporal.getNum()==tmpTemporal.getNum()){
							if(temporal.isEmpty()||tmpTemporal.isEmpty()){
								temporal.clear();
								tmpTemporal.clear();
							}
						}
					}
				}
			}
		}
	}
//clear empty paths,empty dps...and so on int unsafeAssignments unsafePropagation and unsafeTemporal.....
	public static void processEmptyListInResults(){
		if(!unsafeTemporal.isEmpty()){
			List<Temporal> tmpList=new ArrayList<Temporal>();
			tmpList.addAll(unsafeTemporal);
			for(Temporal temporal:tmpList){
				temporal.removeEmptyPath();
				if(temporal.getUnsafePaths().isEmpty())
					unsafeTemporal.remove(temporal);
			}
		}
		if(!unsafePropagation.isEmpty()){
			List<Propagation> tmpList=new ArrayList<Propagation>();
			tmpList.addAll(unsafePropagation);
			for(Propagation propagation:tmpList){
				propagation.removeEmptyPath();
				if(propagation.getUnsafePaths().isEmpty())
					unsafePropagation.remove(propagation);
			}
		}
		if(!unsafeAssignment.isEmpty()){
			List<Assignment> tmpList=new ArrayList<Assignment>();
			tmpList.addAll(unsafeAssignment);
			for(Assignment assignment:tmpList){
				if(assignment.getDps().getDps().isEmpty())
					unsafeAssignment.remove(assignment);
			}
		}
	}
// analysis rules in list ruleAnalysis
	public static void processAllAnalysis(){
		System.out.println("ruleAnalysis Size:"+ruleAnalysis.size());
		if(ruleAnalysis.isEmpty())
			return;
		for(Rule r:ruleAnalysis){
			if(r instanceof Temporal){
				((Temporal)(r)).temporalAnalysis(cfg, unsafeTemporal);
			}
			else if(r instanceof Propagation){
				((Propagation)(r)).propagationAnalysis(cfg, unsafePropagation);
			}
			else if(r instanceof Assignment){
				((Assignment)(r)).assignmentAnalysis(cfg, unsafeAssignment);
			}
			else if(r instanceof Configuration){
				((Configuration)(r)).configurationAnalysis();
			}
			else if(r instanceof ConstantPropagation){
				((ConstantPropagation)(r)).constantPropagationAnalysis(unsafeConstantPropagation);
			}
		}
		
	}
//printResults
	public static void printResults(){
		new ProgramConfig().printResults();
	}
	
//program init
	public static void programInit(){
		new ProgramConfig().programInit();
	}

//if a method hasBody retrun true,else return false
	public static boolean hasBody(SootMethod m){
		if(hasBody.contains(m))
			return true;
		return false;
	}

}
