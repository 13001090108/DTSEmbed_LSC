package softtest.registery.file.generateLicense;

import javax.swing.filechooser.FileSystemView;

public class GenConstants
{
	public final static String OUTPUT_PATH = FileSystemView.getFileSystemView()
			.getDefaultDirectory().getAbsolutePath();

	public final static String SUFFIX = ".dts";
}
