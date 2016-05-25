package Manifest;

import java.io.File;
import java.io.IOException;
import java.io.InputStream;
import java.util.ArrayList;
import java.util.HashSet;
import java.util.Set;
import java.util.zip.ZipEntry;
import java.util.zip.ZipException;
import java.util.zip.ZipFile;

import org.xmlpull.v1.XmlPullParser;

import test.AXMLPrinter;
import android.content.res.AXmlResourceParser;

/**
 * Process the manifest file, and get all components registered statically with
 * their attributes
 * 
 * @author Sophy
 */

public class ProcessManifest {
	private String packageName = "";
	private Set<String> dangerousSet=new HashSet<String>();
	
	public ProcessManifest(File apkFile) {
		ZipFile zipFile;
		try {
			zipFile = new ZipFile(apkFile);
			ZipEntry ze = zipFile.getEntry("AndroidManifest.xml");
			InputStream f = zipFile.getInputStream(ze);
			handleAndroidManifestFile(f);
		} catch (ZipException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		} catch (IOException e) {
			// TODO Auto-generated catch block
			e.printStackTrace();
		}
	}
	public Set<String> getDangerousSet(){
		return this.dangerousSet;
	}

	private void handleAndroidManifestFile(InputStream manifestIS) {
		ArrayList<Component> components=new ArrayList<Component>();
		boolean isPermissionSet=false;
		int index=-1;
		try {
			AXmlResourceParser parser = new AXmlResourceParser();
			parser.open(manifestIS);
			int type = -1;
			while ((type = parser.next()) != XmlPullParser.END_DOCUMENT) {
				switch (type) {
					case XmlPullParser.START_DOCUMENT:
						break;
					case XmlPullParser.START_TAG:
						String tagName = parser.getName();
						if (tagName.equals("manifest")) {
							this.packageName = getAttributeValue(parser, "package");
						}else if (tagName.equals("provider")){
							String isExported = getAttributeValue(parser, "exported");
							String providerName = expandClassName(getAttributeValue(parser, "name"));
							if(isExported.equals("true")){
								dangerousSet.add("DRD01: "+providerName);
							}
						}else if (tagName.equals("application")) {
							String permission=getAttributeValue(parser, "permission");
							String debuggable=getAttributeValue(parser, "debuggable");
							if(permission!=null&&!permission.equals("")){
								isPermissionSet=true;
							}
							if(debuggable!=null&&debuggable.equals("true")){
								dangerousSet.add("DRD10: apk is debuggable");
							}
						}else if (tagName.equals("activity")
								|| tagName.equals("activity-alias")
								|| tagName.equals("receiver")
								|| tagName.equals("service")){
							index++;
							String isExported = getAttributeValue(parser, "exported");
							String componentName = expandClassName(getAttributeValue(parser, "name"));
							String permission=getAttributeValue(parser, "permission");
							if(isExported==null||isExported.equals("")){
								isExported="default";
							}
							switch (tagName) {
							case "activity":
							case "activity-alias":	
								Component activity=new Activity(componentName,isExported,permission); 
								components.add(activity);
								break;
							case "service":
								Component service=new Service(componentName,isExported,permission); 
								components.add(service);
								break;
							case "receiver":
								Component receiver=new Receiver(componentName,isExported,permission); 
								components.add(receiver);
								break;
							default:
								break;
							}
							
						}else if(tagName.equals("intent-filter")){
							components.get(index).intentNumber++;
						}
						break;
					case XmlPullParser.END_TAG:
						tagName = parser.getName();
						if (tagName.equals("activity")
								|| tagName.equals("activity-alias")
								|| tagName.equals("receiver")
								|| tagName.equals("service")){
							index--;
						}
						break;
					case XmlPullParser.TEXT:
						break;
				}
			}
			parser.close();
		} catch (Exception e) {
			e.printStackTrace();
		}
		for(Component component:components){
			if(component instanceof Service){
				if(component.permission!=null&&!component.permission.equals("")){
					isPermissionSet=true;
				}
				if(component.exported.equals("true")||
					(component.exported.equals("default")&&component.intentNumber!=0)){
					if(!isPermissionSet){
						dangerousSet.add("DRD07: "+component.className);
					}
				}
			}else {
				if(component.permission!=null&&!component.permission.equals("")){
					isPermissionSet=true;
				}
				if(component.exported.equals("true")&&component.intentNumber==0&&!isPermissionSet){
					dangerousSet.add("DRD16: "+component.className);
				}
			}
		}
	}

	private String expandClassName(String className) {
		if (className.startsWith("."))
			return this.packageName + className;
		else if (className.substring(0, 1).equals(className.substring(0, 1).toUpperCase()))
			return this.packageName + "." + className;
		else
			return className;
	}

	private static String getAttributeValue(AXmlResourceParser parser,
			String attributeName) {
		for (int i = 0; i < parser.getAttributeCount(); i++) {
			if (parser.getAttributeName(i).equals(attributeName)) {
				return AXMLPrinter.getAttributeValue(parser, i);
			}
		}
		return null;
	}
	
	class Component{
		String className;
		String exported;
		int intentNumber;
		String permission;
		public Component(String className,String exported,String permission){
			this.className=className;
			this.exported=exported;
			this.intentNumber=0;
			this.permission=permission;
		}
	}
	class Activity extends Component{

		public Activity(String className, String exported, String permission) {
			super(className, exported, permission);
			// TODO Auto-generated constructor stub
		}
		
	}
	class Service extends Component{

		public Service(String className, String exported, String permission) {
			super(className, exported, permission);
			// TODO Auto-generated constructor stub
		}
		
	}
	class Receiver extends Component{

		public Receiver(String className, String exported, String permission) {
			super(className, exported, permission);
			// TODO Auto-generated constructor stub
		}
		
	}
}
