package softtest.registery.file.generateLicense;

import java.security.Key;

import javax.crypto.Cipher;
import javax.crypto.SecretKey;
import javax.crypto.SecretKeyFactory;
import javax.crypto.spec.DESKeySpec;

import sun.misc.BASE64Decoder;

class GenEncoder
{
	public static final String ALGORITHM = "DES";

	private static Key toKey(byte[] keyData) throws Exception
	{
//		System.out.println(new String(keyData));
		DESKeySpec dks = new DESKeySpec(keyData);
		SecretKeyFactory keyFactory = SecretKeyFactory.getInstance(ALGORITHM);
		SecretKey secretKey = keyFactory.generateSecret(dks);

		return secretKey;
	}

	private static byte[] decryptBASE64(String key) throws Exception
	{
		return (new BASE64Decoder()).decodeBuffer(key);
	}

	public static Cipher enCipher(String keyStr) throws Exception
	{
		// Key k = toKey(keyStr.getBytes());
		Key k = toKey(decryptBASE64(keyStr));
		Cipher cipher = Cipher.getInstance(ALGORITHM);
		cipher.init(Cipher.ENCRYPT_MODE, k);
		return cipher;
	}
}
