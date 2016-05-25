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
	
	private static String[] expectedPackages =
		{
			"com.facebook",
			"com.google",
			
			"com.twitter",
			"twitter4j",
			
			"com.flurry",			// Yahoo! mobile framework
			
			"com.amazon",
			
			"com.urbanairship"
		};
	
	private static boolean isExpectedClass(SootClass clazz)
	{
		String normalizedPackageName = clazz.getPackageName().toLowerCase();
		
		for (String expectedPackage : expectedPackages)
		{
			if (normalizedPackageName.contains(expectedPackage))
			{
				return true;
			}
		}
		
		return false;
	}
	
	/**
	
	    Scanning package names with first two parts
	    in order to facilitate users to infer plugins
	
	 */
	private static void outputPluginPackages()
	{
		System.out.println("Package prefix related to plugins >>>>>>>>>>>>>>>>>>>>>>>>");
		
		// Here we use set of prefixes
		// since we don't need duplicated package names
		Set<String> packagePrefixes = new TreeSet<String>();
		
		Iterator<SootClass> classIter = Scene.v().getClasses().iterator();
		while (classIter.hasNext())
		{
			SootClass curClass = classIter.next();
			String packageName = curClass.getPackageName();
			if (packageName.startsWith("org")
				|| packageName.startsWith("com"))
			{
				// The package name may contain only two parts
				// e.g. firstPart.secondPart
				int indexOfSecondDot = packageName.indexOf('.', 4);
				String packagePrefix;
				if (indexOfSecondDot == -1)
				{
					// Since the package name only has two parts
					// Record the whole name
					packagePrefix = packageName;
				}
				else
				{
					// Record the beginning two parts of package name
					packagePrefix = packageName.substring(0, indexOfSecondDot);
				}
				
				packagePrefixes.add(packagePrefix);
			}
			else
			{
				// The package name may contain only one part
				// e.g. firstPart
				int indexOfFirstDot = packageName.indexOf('.');
				String packagePrefix;
				if (indexOfFirstDot == -1)
				{
					// Since the package name only has one part
					// Record the whole name
					packagePrefix = packageName;
				}
				else
				{
					// Record the first part of package name
					packagePrefix = packageName.substring(0, indexOfFirstDot);
				}
				
				packagePrefixes.add(packagePrefix);
			}
		}
		
		Iterator<String> packagePrefixIter = packagePrefixes.iterator();
		while (packagePrefixIter.hasNext())
		{
			System.out.println(packagePrefixIter.next());
		}
		
		System.out.println("Package prefix related to plugins <<<<<<<<<<<<<<<<<<<<<<<<");
	}
	
	/**

		Output package name of plug-in classes
		by scanning classes in APK

	 */
	private static void outputPluginClasses()
	{
		System.out.println("Classes related to Facebook/Google/Twitter/Yahoo/Amazon >>>>>>>>>>>>>>>>>>>>>");
		
		Iterator<SootClass> classIter = Scene.v().getClasses().iterator();
		while (classIter.hasNext())
		{
			SootClass curClass = classIter.next();
			if (isExpectedClass(curClass))
			{
				System.out.println(curClass.getName());
			}
		}
		
		System.out.println("Classes related to Facebook/Google/Twitter/Yahoo/Amazon <<<<<<<<<<<<<<<<<<<<<");	
	}
	
	/**
	
	    Output sensitive API calls in apps
	    by scanning methods in classes
	
	 */
	private static void outputSensitiveApiCalls()
	{
		System.out.println("Sensitive API calls >>>>>>>>>>>>>>>>>>>>>");
		
		Iterator<SootClass> classIter = Scene.v().getClasses().iterator();
		while (classIter.hasNext())
		{
			SootClass curClass = classIter.next();
			String curClassFullName = curClass.getName();
			
			//
			// Skip classes in system packages
			if (curClassFullName.startsWith("android"))
			{
				continue;
			}
			
			Iterator<SootMethod> methodIter = curClass.getMethods().iterator();
			while (methodIter.hasNext())
			{
				SootMethod curMethod = methodIter.next();
				String methodFullName = curClassFullName + '.' + curMethod.getName();
				
				// Construct active body for some method
				if (!curMethod.hasActiveBody() && curMethod.isConcrete())
				{
					curMethod.retrieveActiveBody();
				}
					
				// Skip method without active body
				if (!curMethod.hasActiveBody())
				{
					continue;
				}
											
				Iterator<Unit> unitIter = curMethod.getActiveBody().getUnits().iterator();
				while (unitIter.hasNext())
				{
					Unit curUnit = unitIter.next();
					String unitInStringForm = curUnit.toString();
					
					//
					// Location
					
					// android.location.LocationManager.getLastKnownLocation
					if (unitInStringForm.contains("getLastKnownLocation") && unitInStringForm.contains("android.location"))
					{
						System.out.println("Android Location API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// android.location.LocationManager.requestLocationUpdates
					if (unitInStringForm.contains("requestLocationUpdates") && unitInStringForm.contains("android.location"))
					{
						System.out.println("Android Location API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// com.google.android.gms.location.LocationServices
					// Skip classes in Google Play Services SDK
					if (!curClassFullName.contains("com.google.android"))
					{
						if (unitInStringForm.contains("com.google.android.gms.location.LocationServices"))
						{
							System.out.println("Google Play Location API @ " + methodFullName + ':' + unitInStringForm);
						}
					}
					
					//
					// Contacts
					
					// android.provider.ContactsContract.Contacts.CONTENT_URI
					if (unitInStringForm.contains("android.provider.ContactsContract.Contacts") && unitInStringForm.contains("CONTENT_URI"))
					{
						System.out.println("Android Contacts API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// Microphone
					
					// android.media.AudioRecord.read
					if (unitInStringForm.contains("android.media.AudioRecord") && unitInStringForm.contains("read"))
					{
						System.out.println("Android Microphone API @ "+ methodFullName + ':' + unitInStringForm);
					}
					
					//
					// Phone number
					
					// android.telephony.TelephonyManager.getLine1Number
					if (unitInStringForm.contains("android.telephony.TelephonyManager") && unitInStringForm.contains("getLine1Number"))
					{
						System.out.println("Android Telephony Manager API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// Camera
					
					// android.hardware.Camera.takePicture
					if (unitInStringForm.contains("android.hardware.Camera") && unitInStringForm.contains("takePicture"))
					{
						System.out.println("Android Camera API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// android.hardware.camera2.CameraManager.openCamera
					if (unitInStringForm.contains("android.hardware.camera2.CameraManager") && unitInStringForm.contains("openCamera"))
					{
						System.out.println("Android Camera API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// Accelerometer
					
					// android.hardware.Sensor.TYPE_ACCELEROMETER
					if (unitInStringForm.contains("android.hardware.Sensor") && unitInStringForm.contains("TYPE_ACCELEROMETER"))
					{
						System.out.println("Android Accelerometer API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// SMS
					
					// android.provider.Telephony.Sms
					if (unitInStringForm.contains("android.provider.Telephony.Sms"))
					{
						System.out.println("Android SMS API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// IMEI
					
					// android.telephony.TelephonyManager.getDeviceId
					if (unitInStringForm.contains("android.telephony.TelephonyManager") && unitInStringForm.contains("getDeviceId"))
					{
						System.out.println("Android IMEI API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// IMSI
					
					// android.telephony.TelephonyManager.getSubscriberId
					if (unitInStringForm.contains("android.telephony.TelephonyManager") && unitInStringForm.contains("getSubscriberId"))
					{
						System.out.println("Android IMSI API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// ICCID
					
					// android.telephony.TelephonyManager.getSimSerialNumber
					if (unitInStringForm.contains("android.telephony.TelephonyManager") && unitInStringForm.contains("getSimSerialNumber"))
					{
						System.out.println("Android ICCID API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// Device ID
					
					// android.telephony.TelephonyManager.getDeviceId
					if (unitInStringForm.contains("android.telephony.TelephonyManager") && unitInStringForm.contains("getDeviceId"))
					{
						System.out.println("Android Device ID API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// Browser History
					
					// android.provider.Browser
					if (unitInStringForm.contains("android.provider.Browser"))
					{
						System.out.println("Android Browser API @ " + methodFullName + ':' + unitInStringForm);
					}
				}
			}
		}
		
		System.out.println("Sensitive API calls <<<<<<<<<<<<<<<<<<<<<");
	}
	
	/**

		Output the statements calling specified APIs
		by scanning methods in classes

	*/
	private static void outputApiCalls()
	{
		System.out.println("Method call related to Google/Facebook/Twitter/Yahoo/Amazon APIs >>>>>>>>>>>>>>>>>>>>>>>>>");
		
		Set<String> privacyInfoSet = new TreeSet<String>();
		
		// ClassIterator
		Iterator<SootClass> classIter = Scene.v().getClasses().iterator();
		
		while (classIter.hasNext())
		{
			SootClass curClass = classIter.next();
			Iterator<SootMethod> methodIter = curClass.getMethods().iterator();

			//
			// Skip classes in plug-ins package
			// We only inspect classes of app
			//
			// Here we use 'startsWith' instead of 'contains'
			// because apps may use words 'google' in their package names
			String curClassFullName = curClass.getName();
			if (curClassFullName.startsWith("com.google")
				|| curClassFullName.startsWith("android")
				|| curClassFullName.startsWith("com.android")
				
				|| curClassFullName.startsWith("com.facebook")
				
				|| curClassFullName.startsWith("com.twitter")
				|| curClassFullName.startsWith("com.crashlytics")
				|| curClassFullName.startsWith("com.mopub")				// Twitter MoPub
				|| curClassFullName.startsWith("twitter4j")
				
				|| curClassFullName.startsWith("com.amazon")
				
				|| curClassFullName.startsWith("com.flurry"))			// Yahoo! mobile framework
			{
				continue;
			}
			
			while (methodIter.hasNext())
			{
				SootMethod curMethod = methodIter.next();
				String methodFullName = curClassFullName + '.' + curMethod.getName();

				// Construct active body for some method
				if (!curMethod.hasActiveBody() && curMethod.isConcrete())
				{
					curMethod.retrieveActiveBody();
				}
					
				// Skip method without active body
				if (!curMethod.hasActiveBody())
				{
					continue;
				}
											
				Iterator<Unit> unitIter = curMethod.getActiveBody().getUnits().iterator();
				while (unitIter.hasNext())
				{
					Unit curUnit = unitIter.next();
					String unitInStringForm = curUnit.toString();
					
					//
					// Google APIs
						
					// Google Wallet
					
					// Find out call to com.google.android.gms.wallet.Wallet.notifyTransactionStatus
					if (unitInStringForm.contains("getCvn"))
					{
						System.out.println("Google Wallet API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Google Analytics
					
					// Find out call to com.google.android.gms.analytics.GoogleAnalytics.getInstance
					if (unitInStringForm.contains("GoogleAnalytics") && unitInStringForm.contains("getInstance"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.google.android.apps.analytics
					if (unitInStringForm.contains("com.google.android.apps.analytics"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.google.android.gms.analytics.Tracker.enableAdvertisingIdCollection
					if (unitInStringForm.contains("enableAdvertisingIdCollection") && unitInStringForm.contains("Tracker"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Analytics - Advertise ID (Age, Gender, Interest)");
					}
					
					// Find out call to com.google.android.gms.analytics.HitBuilders.EventBuilder
					if (unitInStringForm.contains("HitBuilders") && unitInStringForm.contains("EventBuilder"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Analytics - User Action (EventBuilder)");
					}
					
					// Find out call to com.google.android.gms.analytics.HitBuilders.ScreenViewBuilder
					if (unitInStringForm.contains("HitBuilders") && unitInStringForm.contains("ScreenViewBuilder"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Analytics - Screen View");
					}
					
					// Find out call to com.google.android.gms.analytics.HitBuilders.TransactionBuilder
					if (unitInStringForm.contains("HitBuilders") && unitInStringForm.contains("TransactionBuilder"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Analytics - Shopping Transaction");
					}
					
					// Find out call to com.google.android.gms.analytics.HitBuilders.ItemBuilder
					if (unitInStringForm.contains("HitBuilders") && unitInStringForm.contains("ItemBuilder"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Analytics - Shopping Item");
					}
					
					// Find out call to com.google.android.gms.analytics.ecommerce.Product
					if (unitInStringForm.contains("analytics.ecommerce.Product") && unitInStringForm.contains("com.google"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Analytics - Shopping Product");
					}
					
					// Find out call to com.google.android.gms.analytics.ecommerce.ProductAction
					if (unitInStringForm.contains("analytics.ecommerce.ProductAction") && unitInStringForm.contains("com.google"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Analytics - Shopping Action (Refund/Checkout)");
					}
					
					// Find out call to com.google.android.gms.analytics.ecommerce.Promotion
					if (unitInStringForm.contains("analytics.ecommerce.Promotion") && unitInStringForm.contains("com.google"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Analytics - Shopping Promotion");
					}
						
					// Find out call to com.google.android.gms.analytics.HitBuilders.SocialBuilder
					if (unitInStringForm.contains("HitBuilders") && unitInStringForm.contains("SocialBuilder"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Analytics - Social Action");
					}
					
					// Find out call to com.google.android.gms.analytics.HitBuilders.TimingBuilder
					if (unitInStringForm.contains("HitBuilders") && unitInStringForm.contains("TimingBuilder"))
					{
						System.out.println("Google Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Analytics - User Timing");
					}
					
					// Google+
					
					// Find out call to com.google.android.gms.plus.Plus*
					if (unitInStringForm.contains(".Plus") && unitInStringForm.contains("google"))
					{
						System.out.println("Google+ API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.google.android.gms.plus.model.people.Person
					if (unitInStringForm.contains("com.google.android.gms.plus.model.people.Person"))
					{
						System.out.println("Google+ API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google+ - Personal Profile");
					}
					
					// Find out call to com.google.android.gms.plus.PlusShare.*DeepLink*
					if (unitInStringForm.contains("DeepLink") && unitInStringForm.contains("com.google.android.gms.plus"))
					{
						System.out.println("Google+ API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google+ - Deep Link");
					}
					
					// Google Ads
					
					// Find out call to com.google.android.gms.ads.AdView.setAdUnitId
					if (unitInStringForm.contains("loadAd") && unitInStringForm.contains("google"))
					{
						System.out.println("Google Ads API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.google.android.gms.ads.AdRequest.Builder.addKeyword/setBirthday/setGender/setLocation
					if (unitInStringForm.contains("AdRequest") && unitInStringForm.contains("google"))
					{
						if (unitInStringForm.contains("addKeyword"))
						{
							System.out.println("Google Ads API @ " + methodFullName + ':' + unitInStringForm);
							privacyInfoSet.add("Google Ads - Keywords");
						}
						if (unitInStringForm.contains("setBirthday"))
						{
							System.out.println("Google Ads API @ " + methodFullName + ':' + unitInStringForm);
							privacyInfoSet.add("Google Ads - Birthday");
						}
						if (unitInStringForm.contains("setGender"))
						{
							System.out.println("Google Ads API @ " + methodFullName + ':' + unitInStringForm);
							privacyInfoSet.add("Google Ads - Gender");
						}
						if (unitInStringForm.contains("setLocation"))
						{
							System.out.println("Google Ads API @ " + methodFullName + ':' + unitInStringForm);
							privacyInfoSet.add("Google Ads - Location");
						}
					}
					
					// Find out call to com.google.android.gms.gcm.GCMRegistrar.register
					if (unitInStringForm.contains("GCMRegistrar") && unitInStringForm.contains("register"))
					{
						System.out.println("Google Cloud Messaging API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Google Maps
					
					// Find out call to com.google.android.gms.maps.GoogleMap*
					if (unitInStringForm.contains("GoogleMap"))
					{
						System.out.println("Google Map API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.google.android.maps.*
					if (unitInStringForm.contains("com.google.android.maps"))
					{
						System.out.println("Google Map API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Google Places API
					
					// Find out call related to com.google.android.gms.location.places.Places*
					if (unitInStringForm.contains(".Places") && unitInStringForm.contains("google"))
					{
						System.out.println("Google Places API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.google.android.gms.location.places.AddPlaceRequest
					if (unitInStringForm.contains("AddPlaceRequest") && unitInStringForm.contains("google"))
					{
						System.out.println("Google Places API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Places - Place Add");
					}
					
					// Find out call to com.google.android.gms.location.places.PlaceReport
					if (unitInStringForm.contains("PlaceReport") && unitInStringForm.contains("google"))
					{
						System.out.println("Google Places API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Google Places - Place Report");
					}
					
					// Find out call to com.google.android.gms.games.Games*
					if (unitInStringForm.contains(".Games") && unitInStringForm.contains("google"))
					{
						System.out.println("Google Play Game Service @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.google.android.gms.drive.Drive*
					if (unitInStringForm.contains(".Drive") && unitInStringForm.contains("google"))
					{
						System.out.println("Google Drive API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out statement related to Intent("com.android.vending.billing.InAppBillingService.BIND");
					if (unitInStringForm.contains("com.android.vending.billing.InAppBillingService.BIND"))
					{
						System.out.println("Google Play In-App Billing API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.google.android.gms.fitness.Fitness*
					if (unitInStringForm.contains(".Fitness") && unitInStringForm.contains("google"))
					{
						System.out.println("Google Fit API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to new com.android.vending.LicenseChecker
					if (unitInStringForm.contains("LicenseChecker") && unitInStringForm.contains("com.android"))
					{
						System.out.println("Google Play Licensing API @ "+ methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.google.android.gms.tagmanager.TagManager
					if (unitInStringForm.contains("TagManager") && unitInStringForm.contains("google"))
					{
						System.out.println("Google Tag Manager API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// Facebook APIs
					
					// Find out call to com.facebook.widget.LoginButton
					if (unitInStringForm.contains("LoginButton") && unitInStringForm.contains("facebook"))
					{
						System.out.println("Facebook Login API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.facebook.ads.NativeAd/BannerAd/InterstitalAd.loadAd
					if (unitInStringForm.contains("loadAd") && unitInStringForm.contains("facebook"))
					{
						System.out.println("Facebook ADs API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.facebook.AppEventsLogger
					if (unitInStringForm.contains("AppEventsLogger") && unitInStringForm.contains("facebook"))
					{
						System.out.println("Facebook Analytics API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.facebook.AppEventsLogger.logPurchase
					if (unitInStringForm.contains("AppEventsLogger.logPurchase") && unitInStringForm.contains("facebook"))
					{
						System.out.println("Facebook Analytics API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Facebook Analytics - Purchase Log");
					}
					
					//
					// Twitter APIs
					
					// Twitter - Official APIs
					
					// Find out call to com.twitter.sdk.android.core.identity.TwitterLoginButton
					if (unitInStringForm.contains("TwitterLoginButton"))
					{
						System.out.println("Twitter Login API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.digits.sdk.android.Digits*
					if (unitInStringForm.contains(".Digits") && unitInStringForm.contains("sdk"))
					{
						System.out.println("Twitter Digits Login API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.crashlytics.sdk.android.Crashlytics
					if (unitInStringForm.contains("Crashlytics"))
					{
						System.out.println("Twitter Crashlytics API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.mopub.mobileads.MoPubAd.loadAd
					if (unitInStringForm.contains("loadAd") && unitInStringForm.contains("mopub"))
					{
						System.out.println("Twitter MoPub ADs API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.mopub.nativeads.RequestParameters.Builder
					if (unitInStringForm.contains("RequestParameters") && unitInStringForm.contains("mopub"))
					{
						if (unitInStringForm.contains("keywords"))
						{
							System.out.println("Twitter MoPub ADs API @ " + methodFullName + ':' + unitInStringForm);
							privacyInfoSet.add("Twitter MoPub ADs - Keywords");
						}
						if (unitInStringForm.contains("location"))
						{
							System.out.println("Twitter MoPub ADs API @ " + methodFullName + ':' + unitInStringForm);
							privacyInfoSet.add("Twitter MoPub ADs - Location");
						}
					}
					
					// Find out call to com.mopub.mobileads.MoPubView.setKeywords
					if (unitInStringForm.contains("MoPubView") && unitInStringForm.contains("mopub"))
					{
						System.out.println("Twitter MoPub ADs API @ " + methodFullName + ':' + unitInStringForm);
						privacyInfoSet.add("Twitter MoPub ADs - Keywords");
						
						if (unitInStringForm.contains("m_age"))
						{
							privacyInfoSet.add("Twitter MoPub ADs - Age");
						}
						if (unitInStringForm.contains("m_gender"))
						{
							privacyInfoSet.add("Twitter MoPub ADs - Gender");
						}
						if (unitInStringForm.contains("m_marital"))
						{
							privacyInfoSet.add("Twitter MoPub ADs - Marital");
						}
					}
					
					// Twitter - twitter4j
					
					// Find out call to twitter4j.TwitterFactory.getInstance
					if (unitInStringForm.contains("TwitterFactory") && unitInStringForm.contains("getInstance"))
					{
						System.out.println("twitter4j API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					//
					// Yahoo
					
					// Yahoo Flurry ADs
					
					// Find out call to com.flurry.android.ads.FlurryAds
					if (unitInStringForm.contains("fetchAd") && unitInStringForm.contains("flurry"))
					{
						System.out.println("Yahoo Flurry ADs API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.flurry.android.ads.FlurryAdTargeting.setLocation/setAge/setGender/setKeywords
					if (unitInStringForm.contains("FlurryAdTargeting"))
					{
						System.out.println("Yahoo Flurry ADs API @ " + methodFullName + ':' + unitInStringForm);
						if (unitInStringForm.contains("setLocation"))
						{
							privacyInfoSet.add("Yahoo Flurry ADs - Location");
						}
						if (unitInStringForm.contains("setAge"))
						{
							privacyInfoSet.add("Yahoo Flurry ADs - Age");
						}
						if (unitInStringForm.contains("setGender"))
						{
							privacyInfoSet.add("Yahoo Flurry ADs - Gender");
						}
						if (unitInStringForm.contains("setKeywords"))
						{
							privacyInfoSet.add("Yahoo Flurry ADs - Keywords");
						}
					}
					
					// Find out call to com.flurry.android.FlurryAgent.init
					if (unitInStringForm.contains("FlurryAgent") && unitInStringForm.contains("init"))
					{
						System.out.println("Yahoo Flurry Analytics API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.flurry.android.FlurryAgent.setLocation/setAge/setGender
					if (unitInStringForm.contains("FlurryAgent"))
					{
						if (unitInStringForm.contains("setLocation"))
						{
							privacyInfoSet.add("Yahoo Flurry Analytics - Location");
						}
						if (unitInStringForm.contains("setAge"))
						{
							privacyInfoSet.add("Yahoo Flurry Analytics - Age");
						}
						if (unitInStringForm.contains("setGender"))
						{
							privacyInfoSet.add("Yahoo Flurry Analytics - Gender");
						}
					}
					
					//
					// Amazon
					
					// Amazon SSO
					if (unitInStringForm.contains("AmazonAuthorizationManager"))
					{
						System.out.println("Amazon SSO API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Amazon GameCircle
					if (unitInStringForm.contains("AmazonGamesClient"))
					{
						System.out.println("Amazon GameCircle API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Amazon In-App Purchasing (looking for com.amazon.device.iap.PurchasingService)
					if (unitInStringForm.contains("PurchasingService") && unitInStringForm.contains("com.amazon"))
					{
						System.out.println("Amazon In-App Purchasing API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Amazon Mobile Ads
					if (unitInStringForm.contains("loadAd") && unitInStringForm.contains("com.amazon"))
					{
						System.out.println("Amazon Mobile ADs API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Amazon Mobile Associates (looking for com.amazon.device.associates.AssociatesAPI)
					if (unitInStringForm.contains("AssociatesAPI") && unitInStringForm.contains("com.amazon"))
					{
						System.out.println("Amazon Mobile Associates API @ "+ methodFullName + ':' + unitInStringForm);
					}
					
					// Amazon Device Messaging (looking for com.amazon.device.messaging.ADM)
					if (unitInStringForm.contains("ADM") && unitInStringForm.contains("com.amazon"))
					{
						System.out.println("Amazon Device Messaging API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Amazon Map (looking for com.amazon.geo.mapsv2.AmazonMap
					if (unitInStringForm.contains("AmazonMap") && unitInStringForm.contains("com.amazon"))
					{
						System.out.println("Amazon Map API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Amazon Insights (looking for com.amazon.insights.AmazonInsights.newInstance)
					if (unitInStringForm.contains("AmazonInsights") && unitInStringForm.contains("newInstance"))
					{
						System.out.println("Amazon Insights API @ " + methodFullName + ':' + unitInStringForm);
					}
					
					// Find out call to com.amazonaws.mobileconnectors.amazonmobileanalytics.monetization.GooglePlayMonetizationEventBuilder
					if (unitInStringForm.contains("GooglePlayMonetizationEventBuilder"))
					{
						privacyInfoSet.add("Amazon Insights - Google Play Monetization");
					}
					if (unitInStringForm.contains("AmazonMonetizationEventBuilder"))
					{
						privacyInfoSet.add("Amazon Insights - Amazon Monetization");
					}
					if (unitInStringForm.contains("CustomMonetizationEventBuilder"))
					{
						privacyInfoSet.add("Amazon Insights - Custom Monetization");
					}
					
				}	// Unit Iterator
			}	// Method Iterator
		} // Class Iterator
		
		System.out.println("Method call related to Google/Facebook/Twitter/Yahoo/Amazon APIs <<<<<<<<<<<<<<<<<<<<<<<<<");	
		
		System.out.println("Privacy Info in App >>>>>>>>>>>>>>>>>>>>>>>>>");
		
		Iterator<String> privacyInfoIter = privacyInfoSet.iterator();
		while (privacyInfoIter.hasNext())
		{
			// Print current privacy info
			System.out.println(privacyInfoIter.next());
		}
		
		System.out.println("Privacy Info in App <<<<<<<<<<<<<<<<<<<<<<<<<");
	}
	
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
			
			//
			// Find out all classes in Facebook/Google/Twitter packages
			outputPluginClasses();
			
			//
			// Find out methods call related to various APIs
			outputApiCalls();
			
			//
			// Find out packages related to plugins
			outputPluginPackages();
			
			//
			// Find out sensitive API calls in app
			outputSensitiveApiCalls();
			
			//readRules();
			//process();
			//printResults();
			
			final long finalRun=System.nanoTime();
			System.out.println("analysis time:"+(finalRun-beforeRun)/1000000000 + "seconds");
		}
//		catch (IOException ex) {
//			System.out.println("Cannot read file: " + ex.getMessage());
//			throw new RuntimeException(ex);
//		}
		catch (RuntimeException ex) {
			System.err.println("Exception occurred: " + ex.getMessage());
			ex.printStackTrace();
		}
	}
	
	private static int[] loadViewIdList()
	{
		//
		// Generate default taint list file name
		if (taintFile == null)
		{
			taintFile = apkFile.replace(".apk", ".taint");
		}
		
		System.out.println("Supposed taint file: " + taintFile);
		
		BufferedReader taintFileReader = null;
		try {
			taintFileReader = new BufferedReader(new FileReader(taintFile));
		} catch (FileNotFoundException e) {
			
			//
			// Static analysis without taint file is meaningless
			// So abort program execution with error status
			
			System.err.println("Can't found taint file: " + taintFile);
			System.err.println("Static analysis without taint file is meaningless. Execution aborted");
			
			Runtime.getRuntime().exit(EXIT_STATUS_ERROR);
			
			return new int[0];
		}
		
		ArrayList<Integer> viewIdArrayList = new ArrayList<Integer>();
		try 
		{
			String line = taintFileReader.readLine();
			while (line != null)
			{
				String[] tokens = line.split(" ");
				viewIdArrayList.add(Integer.parseInt(tokens[1]));
				System.out.println("View ID loaded: " + tokens[1]);
				line = taintFileReader.readLine();
			}
			taintFileReader.close();
		}
		catch (IOException e) 
		{	
			e.printStackTrace();
			
			//
			// Return already read data
			int[] viewIdList = new int[viewIdArrayList.size()];
			for (int i=0; i<viewIdArrayList.size(); i++)
			{
				viewIdList[i] = viewIdArrayList.get(i);
			}
			return viewIdList;
		}
		
		//
		// Convert list to array of int
		int[] viewIdList = new int[viewIdArrayList.size()];
		for (int i=0; i<viewIdArrayList.size(); i++)
		{
			viewIdList[i] = viewIdArrayList.get(i);
		}
		return viewIdList;
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
		
		//
		// Load ID list of text view
		//int[] viewIdList = loadViewIdList();
		
		//
		// Make rules
		
		// findViewById
		//Dps dpsViewId = Arg("android.app.Activity.findViewById", 1);
		//Dps dpsView = Ret("android.app.Activity.findViewById");
		//Binds(dpsViewId, dpsView);	
		
		// EditText.getText
		Dps dpsGetText = ArgHierarchy("android.widget.EditText.getText", 0);
		Dps dpsText = Ret("android.widget.EditText.getText");
		Binds(dpsGetText, dpsText);
		
		
		
		//Rule ruleViewId = Assignment(dpsViewId, OneOf(viewIdList));
		//Rule ruleGetText = Propagation(dpsView, dpsGetText, PROP_MAY);
		
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
		
		//Rule[] rules = { ruleViewId, ruleGetText, ruleHttpPost, ruleHttpGet, ruleHttpPut, ruleOutputStream, ruleUrl, ruleUri };
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
