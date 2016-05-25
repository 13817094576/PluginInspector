package Manifest;



import java.io.File;
import java.util.Set;

import tipsticker.Main;

public class ManifestRule {
	public ManifestRule(){
		String apkPath=Main.apkFile;
		File apkFile=new File(apkPath);
		
		Set<String> dangerousSet=(new ProcessManifest(apkFile)).getDangerousSet();
		if(!dangerousSet.isEmpty()){
			for(String dangerousString:dangerousSet){
				Main.unsafeConfiguration.add("Manifest_Rule :"+dangerousString);
			}
		}
	}

}
