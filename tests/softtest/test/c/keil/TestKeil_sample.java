package softtest.test.c.keil;

import softtest.test.c.gcc.BaseTestCase;

import java.io.File;
import java.util.Arrays;
import java.util.Collection;

import org.junit.BeforeClass;
import org.junit.Test;
import org.junit.runner.RunWith;
import org.junit.runners.Parameterized;
import org.junit.runners.Parameterized.Parameters;

import softtest.pretreatment.PlatformType;

@RunWith(Parameterized.class)
public class TestKeil_sample extends BaseTestCase
{
	String path;
	String error;
	
	public TestKeil_sample(String path,String error){
		this.path=path;
		this.error=error;
	}
	
	@BeforeClass
	public static void initPlatformType()
	{	
		setPlatformType(PlatformType.KEIL);
		InitIncludeFiles("C:/Keil/C51/INC");
	}
	
	@Test
	public void test() throws Exception{		
		assert(new File(path).exists());
		if(error.equals("OK")){
			assertTrue("Parsed Failed", test(path));
		}else{
			assertFalse("Parsed should be Failed", test(path));
		}
	}
	
	 @Parameters
	 public static Collection<Object[]> testcaseAndResults(){
		 return Arrays.asList(new Object[][] {
				///////////////////  0   ///////////////////
				{
				"testcase/keilc/ADI 83x/Blinky/Main.c"
				,
				"OK"
				},
				
				///////////////////  1   ///////////////////
				{
				"testcase/keilc/ADI 83x/Extensions/ADI_B2.C"
				,
				"OK"
				},
				
				///////////////////  2   ///////////////////
				{
				"testcase/keilc/Benchmarks/DHRY/DHRY.C"
				,
				"OK"
				},
				
				///////////////////  3   ///////////////////
				{
				"testcase/keilc/Benchmarks/DHRY/README.C"
				,
				"OK"
				},
				
				///////////////////  4   ///////////////////
				{
				"testcase/keilc/Benchmarks/DHRY/TIME.C"
				,
				"OK"
				},
				
				///////////////////  5   ///////////////////
				{
				"testcase/keilc/Benchmarks/SIEVE/SIEVE.C"
				,
				"OK"
				},
				
				///////////////////  6   ///////////////////
				{
				"testcase/keilc/Benchmarks/WHETS/README.C"
				,
				"OK"
				},
				
				///////////////////  7   ///////////////////
				{
				"testcase/keilc/Benchmarks/WHETS/TIME.C"
				,
				"OK"
				},
				
				///////////////////  8   ///////////////////
				{
				"testcase/keilc/Benchmarks/WHETS/WHETS.C"
				,
				"OK"
				},
				
				///////////////////  9   ///////////////////
				{
				"testcase/keilc/BLINKY/BLINKY.C"
				,
				"OK"
				},
				
				///////////////////  10   ///////////////////
				{
				"testcase/keilc/CodeBanking/Bank_EX1/C_BANK0.C"
				,
				"OK"
				},
				
				///////////////////  11   ///////////////////
				{
				"testcase/keilc/CodeBanking/Bank_EX1/C_BANK1.C"
				,
				"OK"
				},
				
				///////////////////  12   ///////////////////
				{
				"testcase/keilc/CodeBanking/Bank_EX1/C_BANK2.C"
				,
				"OK"
				},
				
				///////////////////  13   ///////////////////
				{
				"testcase/keilc/CodeBanking/Bank_EX1/C_ROOT.C"
				,
				"OK"
				},
				
				///////////////////  14   ///////////////////
				{
				"testcase/keilc/CodeBanking/Bank_EX2/C_MESS0.C"
				,
				"OK"
				},
				
				///////////////////  15   ///////////////////
				{
				"testcase/keilc/CodeBanking/Bank_EX2/C_MESS1.C"
				,
				"OK"
				},
				
				///////////////////  16   ///////////////////
				{
				"testcase/keilc/CodeBanking/Bank_EX2/C_PROG.C"
				,
				"OK"
				},
				
				///////////////////  17   ///////////////////
				{
				"testcase/keilc/CodeBanking/Bank_EX3/C_MODUL.C"
				,
				"OK"
				},
				
				///////////////////  18   ///////////////////
				{
				"testcase/keilc/CSAMPLE/CSAMPLE1.C"
				,
				"OK"
				},
				
				///////////////////  19   ///////////////////
				{
				"testcase/keilc/CSAMPLE/CSAMPLE2.C"
				,
				"OK"
				},
				
				///////////////////  20   ///////////////////
				{
				"testcase/keilc/CSAMPLE/CSAMPLE3.C"
				,
				"OK"
				},
				
				///////////////////  21   ///////////////////
				{
				"testcase/keilc/Dallas 390/C/BLINKY.C"
				,
				"OK"
				},
				
				///////////////////  22   ///////////////////
				{
				"testcase/keilc/FarMemory/16MB RAM on ADuC812/MAIN.C"
				,
				"OK"
				},
				
				///////////////////  23   ///////////////////
				{
				"testcase/keilc/FarMemory/1MB Constants on Classic 8051/MAIN.C"
				,
				"OK"
				},
				
				///////////////////  24   ///////////////////
				{
				"testcase/keilc/FarMemory/3 XData Areas on T89C51RD2/Eeprom.c"
				,
				"OK"
				},
				
				///////////////////  25   ///////////////////
				{
				"testcase/keilc/FarMemory/3 XData Areas on T89C51RD2/MAIN.C"
				,
				"OK"
				},
				
				///////////////////  26   ///////////////////
				{
				"testcase/keilc/FarMemory/4MB Variables on Classic 8051/MAIN.C"
				,
				"OK"
				},
				
				///////////////////  27   ///////////////////
				{
				"testcase/keilc/FarMemory/4MB Variables on Classic 8051/Variables.c"
				,
				"OK"
				},
				
				///////////////////  28   ///////////////////
				{
				"testcase/keilc/FarMemory/E2PROM on T89C51RD2/eeprom.c"
				,
				"OK"
				},
				
				///////////////////  29   ///////////////////
				{
				"testcase/keilc/FarMemory/E2PROM on T89C51RD2/MAIN.C"
				,
				"OK"
				},
				
				///////////////////  30   ///////////////////
				{
				"testcase/keilc/HELLO/t.c"
				,
				"OK"
				},
				
				///////////////////  31   ///////////////////
				{
				"testcase/keilc/HELLO/t1.c"
				,
				"OK"
				},
				
				///////////////////  32   ///////////////////
				{
				"testcase/keilc/HELLO.C"
				,
				"OK"
				},
				
				///////////////////  33   ///////////////////
				{
				"testcase/keilc/Infineon C517/GETKEY.C"
				,
				"OK"
				},
				
				///////////////////  34   ///////////////////
				{
				"testcase/keilc/Infineon C517/PUTCHAR.C"
				,
				"OK"
				},
				
				///////////////////  35   ///////////////////
				{
				"testcase/keilc/Infineon C517/README.C"
				,
				"OK"
				},
				
				///////////////////  36   ///////////////////
				{
				"testcase/keilc/Infineon C517/SAMPL517.C"
				,
				"OK"
				},
				
				///////////////////  37   ///////////////////
				{
				"testcase/keilc/Infineon XC864/Blinky/IO.C"
				,
				"OK"
				},
				
				///////////////////  38   ///////////////////
				{
				"testcase/keilc/Infineon XC864/Blinky/MAIN.C"
				,
				"OK"
				},
				
				///////////////////  39   ///////////////////
				{
				"testcase/keilc/Infineon XC864/Blinky/T01.C"
				,
				"OK"
				},
				
				///////////////////  40   ///////////////////
				{
				"testcase/keilc/Infineon XC864/Blinky/UART.C"
				,
				"OK"
				},
				
				///////////////////  41   ///////////////////
				{
				"testcase/keilc/Infineon XC866/ADC/ADC.C"
				,
				"OK"
				},
				
				///////////////////  42   ///////////////////
				{
				"testcase/keilc/Infineon XC866/ADC/IO.C"
				,
				"OK"
				},
				
				///////////////////  43   ///////////////////
				{
				"testcase/keilc/Infineon XC866/ADC/MAIN.C"
				,
				"OK"
				},
				
				///////////////////  44   ///////////////////
				{
				"testcase/keilc/Infineon XC866/Blinky/IO.C"
				,
				"OK"
				},
				
				///////////////////  45   ///////////////////
				{
				"testcase/keilc/Infineon XC866/Blinky/MAIN.C"
				,
				"OK"
				},
				
				///////////////////  46   ///////////////////
				{
				"testcase/keilc/Infineon XC866/Blinky/T01.C"
				,
				"OK"
				},
				
				///////////////////  47   ///////////////////
				{
				"testcase/keilc/Infineon XC866/Blinky/UART.C"
				,
				"OK"
				},
				
				///////////////////  48   ///////////////////
				{
				"testcase/keilc/Infineon XC866/CC6/CC6.C"
				,
				"OK"
				},
				
				///////////////////  49   ///////////////////
				{
				"testcase/keilc/Infineon XC866/CC6/CC6Dave.C"
				,
				"OK"
				},
				
				///////////////////  50   ///////////////////
				{
				"testcase/keilc/Infineon XC866/CC6/IO.C"
				,
				"OK"
				},
				
				///////////////////  51   ///////////////////
				{
				"testcase/keilc/Infineon XC866/CC6/MAIN.C"
				,
				"OK"
				},
				
				///////////////////  52   ///////////////////
				{
				"testcase/keilc/Infineon XC866/CC6/SSC.C"
				,
				"OK"
				},
				
				///////////////////  53   ///////////////////
				{
				"testcase/keilc/Infineon XC866/CC6/T01.C"
				,
				"OK"
				},
				
				///////////////////  54   ///////////////////
				{
				"testcase/keilc/Infineon XC866/CC6/T2.C"
				,
				"OK"
				},
				
				///////////////////  55   ///////////////////
//				{
//				"testcase/keilc/keilc.c"
//				,
//				"OK"
//				},
				
				///////////////////  56   ///////////////////
				{
				"testcase/keilc/keilc_sample.c"
				,
				"OK"
				},
				
				///////////////////  57   ///////////////////
				{
				"testcase/keilc/keil_sample1.c"
				,
				"OK"
				},
				
				///////////////////  58   ///////////////////
				{
				"testcase/keilc/keil_sample2.c"
				,
				"OK"
				},
				
				///////////////////  59   ///////////////////
				{
				"testcase/keilc/keil_sample3.c"
				,
				"OK"
				},
				
				///////////////////  60   ///////////////////
				{
				"testcase/keilc/keil_sample4.c"
				,
				"OK"
				},
				
				///////////////////  61   ///////////////////
				{
				"testcase/keilc/keil_sample5.c"
				,
				"OK"
				},
				
				///////////////////  62   ///////////////////
				{
				"testcase/keilc/keil_sample6.c"
				,
				"OK"
				},
				
				///////////////////  63   ///////////////////
				{
				"testcase/keilc/keil_sample7.c"
				,
				"OK"
				},
				
				///////////////////  64   ///////////////////
				{
				"testcase/keilc/keil_sample8.c"
				,
				"OK"
				},
				
				///////////////////  65   ///////////////////
				{
				"testcase/keilc/keil_sample9.c"
				,
				"OK"
				},
				
				///////////////////  66   ///////////////////
				{
				"testcase/keilc/M8051EW/IBANKING/C_BANK0.C"
				,
				"OK"
				},
				
				///////////////////  67   ///////////////////
				{
				"testcase/keilc/M8051EW/IBANKING/C_BANK1.C"
				,
				"OK"
				},
				
				///////////////////  68   ///////////////////
				{
				"testcase/keilc/M8051EW/IBANKING/C_BANK2.C"
				,
				"OK"
				},
				
				///////////////////  69   ///////////////////
				{
				"testcase/keilc/M8051EW/IBANKING/C_ROOT.C"
				,
				"OK"
				},
				
				///////////////////  70   ///////////////////
				{
				"testcase/keilc/M8051EW/L51IBANK/C_BANK0.C"
				,
				"OK"
				},
				
				///////////////////  71   ///////////////////
				{
				"testcase/keilc/M8051EW/L51IBANK/C_BANK1.C"
				,
				"OK"
				},
				
				///////////////////  72   ///////////////////
				{
				"testcase/keilc/M8051EW/L51IBANK/C_BANK2.C"
				,
				"OK"
				},
				
				///////////////////  73   ///////////////////
				{
				"testcase/keilc/M8051EW/L51IBANK/C_ROOT.C"
				,
				"OK"
				},
				
				///////////////////  74   ///////////////////
				{
				"testcase/keilc/Measure/GETLINE.C"
				,
				"OK"
				},
				
				///////////////////  75   ///////////////////
				{
				"testcase/keilc/Measure/MCOMMAND.C"
				,
				"OK"
				},
				
				///////////////////  76   ///////////////////
				{
				"testcase/keilc/Measure/MEASURE.C"
				,
				"OK"
				},
				
				///////////////////  77   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/C Banking/C_BANK0.C"
				,
				"OK"
				},
				
				///////////////////  78   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/C Banking/C_BANK1.C"
				,
				"OK"
				},
				
				///////////////////  79   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/C Banking/C_ROOT.C"
				,
				"OK"
				},
				
				///////////////////  80   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/C Linear Rom/int.c"
				,
				"OK"
				},
				
				///////////////////  81   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/C Linear Rom/main_a.c"
				,
				"OK"
				},
				
				///////////////////  82   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/C Linear Rom/main_b.c"
				,
				"OK"
				},
				
				///////////////////  83   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/C Linear Rom on MX2/int.c"
				,
				"OK"
				},
				
				///////////////////  84   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/C Linear Rom on MX2/main_a.c"
				,
				"OK"
				},
				
				///////////////////  85   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/C Linear Rom on MX2/main_b.c"
				,
				"OK"
				},
				
				///////////////////  86   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/Large Mem Pool/main.c"
				,
				"OK"
				},
				
				///////////////////  87   ///////////////////
				{
				"testcase/keilc/NXP 80C51MX/Large Mem Pool/POOL.C"
				,
				"OK"
				},
				
				///////////////////  88   ///////////////////
				{
				"testcase/keilc/NXP LPC952/Blinky/Blinky.c"
				,
				"OK"
				},
				
				///////////////////  89   ///////////////////
				{
				"testcase/keilc/NXP LPC954/Blinky/Blinky.c"
				,
				"OK"
				},
				
				///////////////////  90   ///////////////////
				{
				"testcase/keilc/NXP LPC9xx/Blinky/Blinky.c"
				,
				"OK"
				},
				
				///////////////////  91   ///////////////////
				{
				"testcase/keilc/NXP LPC9xx/Hello/Hello.c"
				,
				"OK"
				},
				
				///////////////////  92   ///////////////////
				{
				"testcase/keilc/R8051XC/test_xc.c"
				,
				"OK"
				},
				
				///////////////////  93   ///////////////////
				{
				"testcase/keilc/R8051XC/XBanking/MAIN.C"
				,
				"OK"
				},
				
				///////////////////  94   ///////////////////
				{
				"testcase/keilc/R8051XC/XBanking/Variables.c"
				,
				"OK"
				},
				
				///////////////////  95   ///////////////////
				{
				"testcase/keilc/song.c"
				,
				"OK"
				},
				
				///////////////////  96   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3200/dk3200_dsn_1/dk3200_1_c/DK3200_1_demo.c"
				,
				"OK"
				},
				
				///////////////////  97   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3200/dk3200_dsn_1/dk3200_1_c/upsd3200_adc.c"
				,
				"OK"
				},
				
				///////////////////  98   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3200/dk3200_dsn_1/dk3200_1_c/upsd3200_lcd.c"
				,
				"OK"
				},
				
				///////////////////  99   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3200/dk3200_dsn_1/dk3200_1_c/upsd3200_pwm.c"
				,
				"OK"
				},
				
				///////////////////  100   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3200/dk3200_dsn_1/dk3200_1_c/upsd3200_timer.c"
				,
				"OK"
				},
				
				///////////////////  101   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3200/led_blink/led_blink.c"
				,
				"OK"
				},
				
				///////////////////  102   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3200/led_blink/upsd3200_timer.c"
				,
				"OK"
				},
				
				///////////////////  103   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/Bank0.c"
				,
				"OK"
				},
				
				///////////////////  104   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/Bank1.c"
				,
				"OK"
				},
				
				///////////////////  105   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/Bank2.c"
				,
				"OK"
				},
				
				///////////////////  106   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/Bank3.c"
				,
				"OK"
				},
				
				///////////////////  107   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/Bank4.c"
				,
				"OK"
				},
				
				///////////////////  108   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/banking.c"
				,
				"OK"
				},
				
				///////////////////  109   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/Encoder.c"
				,
				"OK"
				},
				
				///////////////////  110   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/Key.c"
				,
				"OK"
				},
				
				///////////////////  111   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/st85.c"
				,
				"OK"
				},
				
				///////////////////  112   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/upsd3300_adc.c"
				,
				"OK"
				},
				
				///////////////////  113   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/upsd3300_I2C.c"
				,
				"OK"
				},
				
				///////////////////  114   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/upsd3300_lcd.c"
				,
				"OK"
				},
				
				///////////////////  115   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/upsd3300_pca-pwm.c"
				,
				"OK"
				},
				
				///////////////////  116   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/upsd3300_SPI.c"
				,
				"OK"
				},
				
				///////////////////  117   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/Banking/upsd3300_timer.c"
				,
				"OK"
				},
				
				///////////////////  118   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/Bank0.c"
				,
				"OK"
				},
				
				///////////////////  119   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/Bank1.c"
				,
				"OK"
				},
				
				///////////////////  120   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/Bank2.c"
				,
				"OK"
				},
				
				///////////////////  121   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/Bank3.c"
				,
				"OK"
				},
				
				///////////////////  122   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/Bank4.c"
				,
				"OK"
				},
				
				///////////////////  123   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/banking.c"
				,
				"OK"
				},
				
				///////////////////  124   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/Encoder.c"
				,
				"OK"
				},
				
				///////////////////  125   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/Key.c"
				,
				"OK"
				},
				
				///////////////////  126   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/st87.c"
				,
				"OK"
				},
				
				///////////////////  127   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/upsd3300_adc.c"
				,
				"OK"
				},
				
				///////////////////  128   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/upsd3300_I2C.c"
				,
				"OK"
				},
				
				///////////////////  129   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/upsd3300_lcd.c"
				,
				"OK"
				},
				
				///////////////////  130   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/upsd3300_pca-pwm.c"
				,
				"OK"
				},
				
				///////////////////  131   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/Banking/upsd3300_timer.c"
				,
				"OK"
				},
				
				///////////////////  132   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/EEPROM_emul/eeprom.c"
				,
				"OK"
				},
				
				///////////////////  133   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/EEPROM_emul/eeprom_emul_demo.c"
				,
				"OK"
				},
				
				///////////////////  134   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/EEPROM_emul/upsd3300_lcd.c"
				,
				"OK"
				},
				
				///////////////////  135   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/EEPROM_emul/upsd3300_timer.c"
				,
				"OK"
				},
				
				///////////////////  136   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/I2C/I2C_Master/I2C_Master.c"
				,
				"OK"
				},
				
				///////////////////  137   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/I2C/I2C_Master/upsd3300_i2c.c"
				,
				"OK"
				},
				
				///////////////////  138   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/I2C/I2C_Master/upsd3300_lcd.c"
				,
				"OK"
				},
				
				///////////////////  139   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/I2C/I2C_Master/upsd3300_timer.c"
				,
				"OK"
				},
				
				///////////////////  140   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/I2C/I2C_Slave/I2C_Slave.c"
				,
				"OK"
				},
				
				///////////////////  141   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/I2C/I2C_Slave/upsd3300_i2c.c"
				,
				"OK"
				},
				
				///////////////////  142   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/I2C/I2C_Slave/upsd3300_lcd.c"
				,
				"OK"
				},
				
				///////////////////  143   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/I2C/I2C_Slave/upsd3300_timer.c"
				,
				"OK"
				},
				
				///////////////////  144   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/LED_Blink/led_blink.c"
				,
				"OK"
				},
				
				///////////////////  145   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/LED_Blink/upsd3300_timer.c"
				,
				"OK"
				},
				
				///////////////////  146   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/PWM_ADC/pwm_adc.c"
				,
				"OK"
				},
				
				///////////////////  147   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/PWM_ADC/upsd3300_adc.c"
				,
				"OK"
				},
				
				///////////////////  148   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/PWM_ADC/upsd3300_lcd.c"
				,
				"OK"
				},
				
				///////////////////  149   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/PWM_ADC/upsd3300_pca-pwm.c"
				,
				"OK"
				},
				
				///////////////////  150   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/PWM_ADC/upsd3300_timer.c"
				,
				"OK"
				},
				
				///////////////////  151   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/SPI/spi_demo.c"
				,
				"OK"
				},
				
				///////////////////  152   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/SPI/upsd3300_lcd.c"
				,
				"OK"
				},
				
				///////////////////  153   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/SPI/upsd3300_spi.c"
				,
				"OK"
				},
				
				///////////////////  154   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/DK3300-ELCD/SPI/upsd3300_timer.c"
				,
				"OK"
				},
				
				///////////////////  155   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/LED_Blink/led_blink.c"
				,
				"OK"
				},
				
				///////////////////  156   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/LED_Blink/upsd3300_timer.c"
				,
				"OK"
				},
				
				///////////////////  157   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/PWM_ADC/pwm_adc.c"
				,
				"OK"
				},
				
				///////////////////  158   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/PWM_ADC/upsd3300_adc.c"
				,
				"OK"
				},
				
				///////////////////  159   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/PWM_ADC/upsd3300_lcd.c"
				,
				"OK"
				},
				
				///////////////////  160   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/PWM_ADC/upsd3300_pca-pwm.c"
				,
				"OK"
				},
				
				///////////////////  161   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3300/PWM_ADC/upsd3300_timer.c"
				,
				"OK"
				},
				
				///////////////////  162   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3400/LCD_DEMO/LCD_demo.c"
				,
				"OK"
				},
				
				///////////////////  163   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3400/LCD_DEMO/upsd3400_lcd.c"
				,
				"OK"
				},
				
				///////////////////  164   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3400/LCD_DEMO/upsd3400_timer.c"
				,
				"OK"
				},
				
				///////////////////  165   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3400/LED_BLINK/led_blink.c"
				,
				"OK"
				},
				
				///////////////////  166   ///////////////////
				{
				"testcase/keilc/ST uPSD/upsd3400/LED_BLINK/upsd3400_timer.c"
				,
				"OK"
				},
				
				///////////////////  167   ///////////////////
				{
				"testcase/keilc/TI MSC1200/AD4Input/AD4Input.c"
				,
				"OK"
				},
				
				///////////////////  168   ///////////////////
				{
				"testcase/keilc/TI MSC121x/AD4Input/AD4Input.c"
				,
				"OK"
				},
				
				///////////////////  169   ///////////////////
				{
				"testcase/keilc/TI MSC121x/AD8Input/AD8Input.c"
				,
				"OK"
				},
				
				///////////////////  170   ///////////////////
				{
				"testcase/keilc/TI MSC121x/AD_Interupt/AD_Interrupt.c"
				,
				"OK"
				},
		 });
		 }
}
