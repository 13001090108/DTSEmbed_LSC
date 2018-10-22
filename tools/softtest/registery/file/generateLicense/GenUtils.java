package softtest.registery.file.generateLicense;

import java.io.File;
import java.io.FileOutputStream;
import java.io.ObjectOutputStream;

import javax.crypto.Cipher;
import javax.crypto.CipherOutputStream;

class GenUtils
{

	public static void saveToEncryptFile(String key, Object data, String path,
			String name)
	{
		File file = new File(path);
		if (!file.exists())
			file.mkdirs();

		FileOutputStream fout = null;
		CipherOutputStream cout = null;
		ObjectOutputStream out = null;
		try
		{
			fout = new FileOutputStream(new File(file, name));
			Cipher cipher = GenEncoder.enCipher(key);
			cout = new CipherOutputStream(fout, cipher);
			out = new ObjectOutputStream(cout);
			out.writeObject(data);
		}
		catch (Exception ex)
		{
		}
		finally
		{
			try
			{
				if (out != null)
					out.close();
				else
					if (cout != null)
						cout.close();
					else
						if (fout != null)
							fout.close();
			}
			catch (Exception ex)
			{
			}
		}
	}

}
