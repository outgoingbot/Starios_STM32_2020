/* USER CODE BEGIN Header */
/**FS
 *
  ******************************************************************************
  * @file           : main.c
  * @brief          : Main program body
  ******************************************************************************
  * @attention
  WS2812 spi dma
  goals
  1)use SPI with DMA to write a neoPixel Function stack   <------- DONE. SPI requires 2.25MHz to 2.5MHz clock speed
  2)Write a matrix library that can perform many common transformations. Translations, rotations, scale, skew, etc
  3)Integrate the FTT c library into this code to do Fast Fourier Transform on AUdio data without the need of MSGEQ7 icd  <------ DONE 90%
  4)write Battery Monitor Gauge function
  ---PINOUTS----
  -OLED -> PB6=SCK, PB7=SDA, PB1=RST (OUTPUT)
  -RGB -> PB15 (SPI2 MOSI)
  -MEMS AUDIO -> PA0 (Analog INPUT)
  -Battery Monitor -> PA1 (Analog INPUT)
  -Battery Monitor Enable -> PA2 (OUTPUT)
  -USB Connected Monitor -> PA3 (INPUT) ~2.5v Connected
  -USB Detect/Enable -> PB9 (low at boot, High when PA3 is active)
  -Soft Power -> PB8 (OUTPUT)
  -Buzzer -> PB0 (OUTPUT) *change to timer PWM-Mode output
  -Buttons -> BTN1=PB3 (INPUT), BTN2=PB4 (INPUT), BTN3=PB5 (PULL-UP INPUT) // All Active LOW
  -USB -> PA11, PA12 //having issue where USB data Pins are powering on the device <--Fixed using PB9 OUTPUT HIGH (3v3) when PA3 VBUS Detect INPUT HIGH.

   BOOT0: LOW = RUN, HIGH = PROGRAM

   *****ISSUES:
   	   	   	   1) Boot0 Pin State is confusing me. it seems to work either high or low now
   	   	   	   2) ADC1 (read_bat_adc) is slowing down the Audio Sampling. battery should only be checked every few minutes
   	   	   	   3) USB Virtual Serial Port Is only working if device is already on. <-- Fixed. note above

   ******Need to Write:
   	   	 1)Soft Power
   	   	 2)Noise Calibration & Auto Leveler(uses timer. maybe able to use FFT Timer)
   	   	 4)Function to pass-in a BIN value and have it Map to n-size output. used in all audio mode animations. instead of mapping in each animation
   	   	 5)Write a matrix library that can perform many common transformations. Translations, rotations, scale, skew, etc


how to program?
1) have Oled and RGB that update based on timer. i.e. at 30Hz. no matter what, update the display with what ever is in the buffer
2) for every action change the buffer and show

audio functions: Most readings are using a simple moving average i.e (current + previous) / 2

	INIT) Calibrate Mic. run this by holding BTN1 at boot. All it does: adjustvals();, shows bar graph. write EEPROM
		-if(calibrationFlag) Store Readings into NoisePCB[i] Array

	1) Adjust Vals: does 2 things. filters raw data and updates (increases) highthresh[i] as needed.
		-valS[i] = Rawvalue[i] - lowThresh[i] - NoisePCB[i]

		-highthresh[i] Minimum is lowthresh[i] + hOffset.  hOffset is just some fixed number, 6 is used on the atmel version
		-highThresh[i] is increased to ValS[i] if valS[i] > highthresh[i].
				interestingly. ValS[i] must also be < highthresh[i] + (2*hOffset).
				i think this is to prevent much larger signals from changing highthresh[i] too much too quickly
				in the mean time, in the ISR, highthresh[i]-- is pccuring every ISR cycle.
		-lowThresh[i] is only set manually using an exponential function.

	2) MSGEQ7 Mode
		-updateLowHighThresh(); - This function is mainly to manually update lowthresh[i] with a button press, and also resets highthresh[i] = lowthresh[i] + hOffset
		-Turn Hardware Sample Timer ON (ISR) -get raw data from fft. (really a running average) and perform highthresh[i]-- (or similar)
		-Run AdjustVals();  -listed above. remove noise and lowthresh from raw data. updates high thresh
		-Signal-Size Mapping. Does "need to write #4" (above) for each animation
		-map N dist and/or brightness/special mode action(high bass) to some sort of pre-defines vector. animations suck becuase they are based off static geometry.
		   	-yDist = (valS[i]*numRows) / (highThresh[i]-lowThresh[i]) // example of a mapping function with inMin = 0 and OutMin = 0
		-Show();

++STOPPED HERE. REVIEW ABOVE #2


-a better approach?
	0) calibration needs to exist? performed when it is quiet. maybe use the map() and set lowthresh[i] = NoisePCB[i] at boot? to omit any calibration?
	1)  Start Timer
	    Windowing()
		FFT()
		adjustVals() (perform filtering, increase highthresh[i] as needed, perform highthresh[i]-- (decrease over time interval), running average?
		Stop Timer
	2)update RGB animation() - need access to valS[i], yDist, rDist,gDist,bDist. write functions that can return those. perhaps others?
	3)checkbuttons()
	  -at a slower interval: analog read battery and check USB
	4)show OLED();
	  show RGB();


-There is a random number function I wrote to simplify getting a random number
-I have the stm32 outputting serial data on USb detect
  ******************************************************************************
  */
/* USER CODE END Header */

/* Includes ------------------------------------------------------------------*/
#include "main.h"
#include "usb_device.h"

/* Private includes ----------------------------------------------------------*/
/* USER CODE BEGIN Includes */
//#include "stm32f1xx_it.h"
#include "stdlib.h"
#include "string.h"
#include "math.h"

#include "bittable.h"
#include "Chartable.h"
#include "matrixLayout.h"

#include "ssd1306.h"
#include "fonts.h"
#include "bitmap.h"
#include "eeprom.h"
USBD_HandleTypeDef hUsbDeviceFS;
/* USER CODE END Includes */

/* Private typedef -----------------------------------------------------------*/
/* USER CODE BEGIN PTD */

/* USER CODE END PTD */

/* Private define ------------------------------------------------------------*/
/* USER CODE BEGIN PD */
#define NUMLEDS 168 //number of leds 128 or 168 or 121 (168 has dummy columns)
#define EXPANDFACTOR 9 // 3 bytes to SPI for 1 byte of color. green or red or blue
#define SPILOWTIME 30 //(30 for rgb3535) this is calculated on spi clock speed. it needs to be 50us of spi 0 bytes
#define BMAX 11*4//11
#define BMED 6*4//6
#define BMIN 2*4

#define numCols 21
#define numRows 8
//#define RAND_MAX 32767

//Leds are G,R,B
#define BLACK 0x000000
#define GREEN 0x0A0000
#define RED 0x000A00
#define BLUE 0x00000A

#define N	128 //64
#define PI	3.14159265
#define FFT_LIB_REV 0x14
#define FFT_FORWARD 0x01
#define FFT_REVERSE 0x00
#define FFT_WIN_TYP_RECTANGLE 0x00 /* rectangle (Box car) */
#define FFT_WIN_TYP_HAMMING 0x01 /* hamming */
#define FFT_WIN_TYP_HANN 0x02 /* hann */
#define FFT_WIN_TYP_TRIANGLE 0x03 /* triangle (Bartlett) */
#define FFT_WIN_TYP_NUTTALL 0x04 /* nuttall */
#define FFT_WIN_TYP_BLACKMAN 0x05 /* blackman */
#define FFT_WIN_TYP_BLACKMAN_NUTTALL 0x06 /* blackman nuttall */
#define FFT_WIN_TYP_BLACKMAN_HARRIS 0x07 /* blackman harris*/
#define FFT_WIN_TYP_FLT_TOP 0x08 /* flat top */
#define FFT_WIN_TYP_WELCH 0x09 /* welch */
#define twoPi 6.28318531
#define fourPi 12.56637061
#define sixPi 18.84955593

/* USER CODE END PD */

/* Private macro -------------------------------------------------------------*/
/* USER CODE BEGIN PM */

/* USER CODE END PM */

/* Private variables ---------------------------------------------------------*/
ADC_HandleTypeDef hadc1;
ADC_HandleTypeDef hadc2;

I2C_HandleTypeDef hi2c1;

SPI_HandleTypeDef hspi2;
DMA_HandleTypeDef hdma_spi2_tx;

TIM_HandleTypeDef htim3;

/* USER CODE BEGIN PV */

/* USER CODE END PV */

/* Private function prototypes -----------------------------------------------*/
void SystemClock_Config(void);
static void MX_GPIO_Init(void);
static void MX_DMA_Init(void);
static void MX_SPI2_Init(void);
static void MX_ADC1_Init(void);
static void MX_I2C1_Init(void);
static void MX_TIM3_Init(void);
static void MX_ADC2_Init(void);
/* USER CODE BEGIN PFP */
void setPixelColor(int,uint32_t);
uint32_t getPixelColor(int);
void show(void);
void getrand(int);
long map(long, long, long, long, long);
void HorizShiftR(void);
void HorizShiftL(void);
void rotateCCW(uint32_t);
void sine1 (uint32_t);
void nBalls (void);
void nGrid (void);
void splash(void);
uint32_t Color(uint8_t,uint8_t,uint8_t);
void BlankScreen(uint32_t);
void printCharWithShiftL(char, int);
void printStringWithShiftL(char*, int);
int randomNum(int, int);

void graphMAG(void);
void graphMAG_ADJUSTED(void);
uint16_t read_adc (void);
uint16_t read_bat_adc(void);
void ComputeFFT(double* , double* , uint16_t , uint8_t , uint8_t);
void ComplexToMagnitude(double* , double* , uint16_t);
uint8_t Exponent(uint16_t);
void Swap(double* , double*);
void Windowing(double* , uint16_t , uint8_t , uint8_t);
double sq(double);
void updateLowHighThresh(void);
void adjustVals(void);
uint16_t audioMap(int, int, int);

int checkbuttons(void);
int checkUSBConnected(void);
void USBdataEnable(int);

extern uint8_t CDC_Transmit_FS(uint8_t*, uint16_t); //prototype of external usb transmit
//need a usb receive function
/* USER CODE END PFP */

/* Private user code ---------------------------------------------------------*/
/* USER CODE BEGIN 0 */

uint8_t myData[(NUMLEDS*EXPANDFACTOR)+SPILOWTIME]; //holds all the expanded Pixel Color data + the 50uS of zero time (WS2812 reset)
uint32_t Forecolor = 0x000800;
uint8_t Brange = BMIN; //1,6,11  //set the brightness for each chanel in getrand();
uint8_t green; //used in getrand
uint8_t red;   //used in getrand
uint8_t blue;  //used in getrand
uint8_t mbuffer[3];   //used for scroll text

uint32_t ArrayBuffer[8] = {0, 0, 0, 0, 0, 0, 0, 0}; //this can be local?
int randSelect = 0;
int cycles = 10;
uint32_t waittime = 200;
char myString[] = "H3llo "; //used to test USB virutal COM Port Transmit


volatile uint16_t adc_value = 0; //holds ADC0 value
volatile uint8_t n_count = 0; //indexes hgihwater count
volatile uint8_t n_done = 0; //flag to perform fft operations
double REX[N]; //holds Real input and Realoutput (overwritten when windowing/computeFFT is performed
double IMX[N]; //hold imaginary output
int MAG[N];//magnitude of a+bi vector
const uint16_t mySamples = N; //needs to match #define N

uint32_t threshLevel=0;
uint32_t threshWater=1000;
uint32_t hOffset = 32; //somewhere around 25 to 50 seems good. if this is too low the screen will "max out"
uint32_t highThresh[N];
uint32_t lowThresh[N];
uint32_t micLevel = 2;

const int tones[6] = {1, 1, 2, 2, 1 ,2}; //these are like pitches
const int tonedelay[6]={1,1,1,1,1,1}; //these are duration delays

uint16_t batteryLevel = 0;

/* Virtual address defined by the user: 0xFFFF value is prohibited */
uint16_t VirtAddVarTab[NB_OF_VAR] = {0x5555, 0x6666, 0x7777};
uint16_t VarDataTab[NB_OF_VAR] = {0, 0, 0};
uint16_t VarValue = 0;
/* USER CODE END 0 */

/**
  * @brief  The application entry point.
  * @retval int
  */
int main(void)
{
  /* USER CODE BEGIN 1 */

  /* USER CODE END 1 */

  /* MCU Configuration--------------------------------------------------------*/

  /* Reset of all peripherals, Initializes the Flash interface and the Systick. */
  HAL_Init();

  /* USER CODE BEGIN Init */

  /* USER CODE END Init */

  /* Configure the system clock */
  SystemClock_Config();

  /* USER CODE BEGIN SysInit */

  /* USER CODE END SysInit */

  /* Initialize all configured peripherals */
  MX_GPIO_Init();
  MX_DMA_Init();
  MX_SPI2_Init();
  MX_ADC1_Init();
  MX_I2C1_Init();
  MX_TIM3_Init();
  MX_ADC2_Init();
  MX_USB_DEVICE_Init();
  /* USER CODE BEGIN 2 */

//SETUP
    //Power INIT
  HAL_Delay(500); //wait .5 sec before power on. prevents false positives
  HAL_GPIO_WritePin(GPIOB,GPIO_PIN_8, GPIO_PIN_SET);//SoftPower ON
  //HAL_GPIO_WritePin(GPIOB,GPIO_PIN_8, GPIO_PIN_RESET);//SoftPower OFF

  //REQUIRED to set all the end frame bytes to zero (50uS ws2812 reset)
  for (int x=(NUMLEDS*EXPANDFACTOR); x<(NUMLEDS*EXPANDFACTOR)+SPILOWTIME; x++) myData[x] = 0;
  for (int i=0; i<N; i++)highThresh[i] = hOffset;
  /* Unlock the Flash Program Erase controller */
 // HAL_FLASH_Unlock();

  /* EEPROM Init */
 // EE_Init();

  SSD1306_Init();  // initialize (modified ssd1306.c with reset pin code)

  HAL_ADC_Start(&hadc1); //starts the adc configured in continuous mode (cubeMX)

  HAL_ADC_Start(&hadc2); //start adc2 in continuous mode

updateLowHighThresh(); //set lowThresh and HighThresh

SSD1306_GotoXY (0,0);
SSD1306_Clear();
SSD1306_DrawBitmap(0,0,Boot, 128, 32, 1);
SSD1306_UpdateScreen(); //display
HAL_Delay (500);
SSD1306_Clear();

BlankScreen(BLACK);
printStringWithShiftL(" STARIOS GEAR 2020   ", 40); //Send Lscrolling Text (send car array)
BlankScreen(BLACK);


for(int i=0; i<6; i++){//buzzer test.
  for(int x=0; x<tonedelay[i]*40; x++){
    HAL_GPIO_WritePin(GPIOB,GPIO_PIN_0, GPIO_PIN_SET);
    HAL_Delay(tones[i]);
    HAL_GPIO_WritePin(GPIOB,GPIO_PIN_0, GPIO_PIN_RESET);
    HAL_Delay(tones[i]);
  }
  HAL_Delay(tonedelay[i]*25);
}


/*
for(int c=0; c<3; c++){ //mesing around with some animations 3 floating heads i guess
  for(int x=0; x<128; x+=4){
  SSD1306_Clear();
  SSD1306_DrawBitmap(x,(uint16_t) 16 + 16*sin(2*PI*x/128),face, 16, 16, 1); //bitmaps need to be powers of 2?
  SSD1306_DrawBitmap(x,(uint16_t) 20 + 16*sin(2*PI*x/64),face, 16, 16, 1);
  SSD1306_DrawBitmap(x,(uint16_t) 24 + 16*sin(2*PI*x/32),face, 16, 16, 1);
  SSD1306_UpdateScreen(); //display
  }
}
*/
  /* USER CODE END 2 */

  /* Infinite loop */
  /* USER CODE BEGIN WHILE */

while (1){
    /* USER CODE END WHILE */

    /* USER CODE BEGIN 3 */

/*
	//RGB TEST
	cycles = 10;
	BlankScreen(BLACK);
	for(int x=0; x<1; x++){
	  BlankScreen(RED);
	  HAL_Delay(5000);
	  BlankScreen(GREEN);
	  HAL_Delay(5000);
	  BlankScreen(BLUE);
	  HAL_Delay(5000);
	}
*/

/*
	for(int x=0; x<2; x++){
	  waittime = 3000;
	  getrand(0);
	  BlankScreen(Forecolor);
	  HAL_Delay(waittime);
	}
*/
//END RGB TESTs


HAL_TIM_Base_Start_IT(&htim3); //start Timer 3. used for FFT sampling

for(int x=0; x<10000; x++){ 											//long loop for testing FFT (working pretty will)
	while (!n_done); 													// empty loop until N ADC's have occured in the TIM3 ISR
	for (int i = 0; i < mySamples; i++) IMX[i] = 0.0; 					//zero out complex part before FFT
	Windowing(REX, mySamples, FFT_WIN_TYP_HANN, FFT_FORWARD);		//HANN	//Apply Window the the ADC data
	ComputeFFT(REX, IMX, mySamples, Exponent(mySamples),FFT_FORWARD); 	//perform the exponent in setup to optimize
	HAL_TIM_Base_Stop_IT(&htim3); 										//stop Timer 3

	SSD1306_Puti(0, 6, 7-checkbuttons(), 1); 							//print button press TESTING

	if(x%200==0) batteryLevel = read_bat_adc(); //only update the battery monitor every 1000

	SSD1306_Puti(20, 6, batteryLevel, 4); //print battery level test
	SSD1306_DrawFilledRectangle(20, 0, (uint16_t) map(batteryLevel,0,4096,0,80) , 2 , 1); //only run this every few minutes or so
	if(checkUSBConnected()){
		USBdataEnable(1); //enable USB Data+ (DP)
		SSD1306_GotoXY (100,0);
		SSD1306_Puts ("USB", &Font_7x10, 1);; //1 if USB plugged in, 0 if not plugged in
		//USB Virtual serial Port send string
		char str[6]; //23 change this based on the string + data + newline+string null, etc
		//sprintf(str, "Battery Level = %04ld \n", batteryLevel); //sprintf is complainging becuase using uint8_t instead of char
		sprintf(str, "%04ld\n", batteryLevel); //sprintf is complainging becuase using uint8_t instead of char
		if(x%200==0) CDC_Transmit_FS(str, sizeof(str)); //prints color value to USB virtual serial port //send a test message
	}else{
		USBdataEnable(0); //Disable USB Data+ (DP)
	}


	//graphMAG(); //graph the complex magnitudes on the oled
	graphMAG_ADJUSTED(); //graph the complex magnitudes on the oled
	HAL_TIM_Base_Start_IT(&htim3); //start Timer 3
	n_done = 0;
}

HAL_TIM_Base_Stop_IT(&htim3); //stop Timer 3 //needed to prevent weird RGB led shit


	cycles = 1000;
	BlankScreen(BLACK);
	for(int x=0; x<10; x++){
	  waittime = 30;
	  getrand(0);
	  sine1(waittime);
	}

	cycles = 1000;
	waittime = 30;
	BlankScreen(BLACK);
	printStringWithShiftL(" STARIOS GEAR 2020   ", 40); //Send Lscrolling Text (send car array)



/*
	cycles = 4;
		waittime = 10;
		BlankScreen(0x000000);
		for(int x=0; x<500; x++){
			rotateCCW(45); //WIP
		}

*/
	cycles = 4;

	BlankScreen(BLACK);
	for(int x=0; x<500; x++){
		waittime = 10;
		nGrid();
	}


	cycles = 1000;
	waittime = 30;
	BlankScreen(BLACK);
	for(int x=0; x<10; x++){
		waittime = 30;
	  //getrand(0);
	  sine1(waittime);
	}


	cycles = 500;
	waittime = 20;
	BlankScreen(BLACK);
	for(int x=0; x<4; x++){
	  nBalls();
	}



	//test pattern
	BlankScreen(BLACK);
	getrand(0);
	setPixelColor(0, Forecolor); //set first pixel a random color
	show();
	HAL_Delay(500);
	for(int x=0; x<NUMLEDS; x++){
	  setPixelColor(x, getPixelColor(0)); //set first pixel green
	  show();
	  HAL_Delay(20);
	}


  }
  /* USER CODE END 3 */
}

/**
  * @brief System Clock Configuration
  * @retval None
  */
void SystemClock_Config(void)
{
  RCC_OscInitTypeDef RCC_OscInitStruct = {0};
  RCC_ClkInitTypeDef RCC_ClkInitStruct = {0};
  RCC_PeriphCLKInitTypeDef PeriphClkInit = {0};

  /** Initializes the CPU, AHB and APB busses clocks 
  */
  RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSE;
  RCC_OscInitStruct.HSEState = RCC_HSE_ON;
  RCC_OscInitStruct.HSEPredivValue = RCC_HSE_PREDIV_DIV1;
  RCC_OscInitStruct.HSIState = RCC_HSI_ON;
  RCC_OscInitStruct.PLL.PLLState = RCC_PLL_ON;
  RCC_OscInitStruct.PLL.PLLSource = RCC_PLLSOURCE_HSE;
  RCC_OscInitStruct.PLL.PLLMUL = RCC_PLL_MUL9;
  if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK)
  {
    Error_Handler();
  }
  /** Initializes the CPU, AHB and APB busses clocks 
  */
  RCC_ClkInitStruct.ClockType = RCC_CLOCKTYPE_HCLK|RCC_CLOCKTYPE_SYSCLK
                              |RCC_CLOCKTYPE_PCLK1|RCC_CLOCKTYPE_PCLK2;
  RCC_ClkInitStruct.SYSCLKSource = RCC_SYSCLKSOURCE_PLLCLK;
  RCC_ClkInitStruct.AHBCLKDivider = RCC_SYSCLK_DIV1;
  RCC_ClkInitStruct.APB1CLKDivider = RCC_HCLK_DIV2;
  RCC_ClkInitStruct.APB2CLKDivider = RCC_HCLK_DIV1;

  if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_2) != HAL_OK)
  {
    Error_Handler();
  }
  PeriphClkInit.PeriphClockSelection = RCC_PERIPHCLK_ADC|RCC_PERIPHCLK_USB;
  PeriphClkInit.AdcClockSelection = RCC_ADCPCLK2_DIV6;
  PeriphClkInit.UsbClockSelection = RCC_USBCLKSOURCE_PLL_DIV1_5;
  if (HAL_RCCEx_PeriphCLKConfig(&PeriphClkInit) != HAL_OK)
  {
    Error_Handler();
  }
}

/**
  * @brief ADC1 Initialization Function
  * @param None
  * @retval None
  */
static void MX_ADC1_Init(void)
{

  /* USER CODE BEGIN ADC1_Init 0 */

  /* USER CODE END ADC1_Init 0 */

  ADC_ChannelConfTypeDef sConfig = {0};

  /* USER CODE BEGIN ADC1_Init 1 */

  /* USER CODE END ADC1_Init 1 */
  /** Common config 
  */
  hadc1.Instance = ADC1;
  hadc1.Init.ScanConvMode = ADC_SCAN_DISABLE;
  hadc1.Init.ContinuousConvMode = ENABLE;
  hadc1.Init.DiscontinuousConvMode = DISABLE;
  hadc1.Init.ExternalTrigConv = ADC_SOFTWARE_START;
  hadc1.Init.DataAlign = ADC_DATAALIGN_RIGHT;
  hadc1.Init.NbrOfConversion = 1;
  if (HAL_ADC_Init(&hadc1) != HAL_OK)
  {
    Error_Handler();
  }
  /** Configure Regular Channel 
  */
  sConfig.Channel = ADC_CHANNEL_0;
  sConfig.Rank = ADC_REGULAR_RANK_1;
  sConfig.SamplingTime = ADC_SAMPLETIME_1CYCLE_5;
  if (HAL_ADC_ConfigChannel(&hadc1, &sConfig) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN ADC1_Init 2 */

  /* USER CODE END ADC1_Init 2 */

}

/**
  * @brief ADC2 Initialization Function
  * @param None
  * @retval None
  */
static void MX_ADC2_Init(void)
{

  /* USER CODE BEGIN ADC2_Init 0 */

  /* USER CODE END ADC2_Init 0 */

  ADC_ChannelConfTypeDef sConfig = {0};

  /* USER CODE BEGIN ADC2_Init 1 */

  /* USER CODE END ADC2_Init 1 */
  /** Common config 
  */
  hadc2.Instance = ADC2;
  hadc2.Init.ScanConvMode = ADC_SCAN_DISABLE;
  hadc2.Init.ContinuousConvMode = ENABLE;
  hadc2.Init.DiscontinuousConvMode = DISABLE;
  hadc2.Init.ExternalTrigConv = ADC_SOFTWARE_START;
  hadc2.Init.DataAlign = ADC_DATAALIGN_RIGHT;
  hadc2.Init.NbrOfConversion = 1;
  if (HAL_ADC_Init(&hadc2) != HAL_OK)
  {
    Error_Handler();
  }
  /** Configure Regular Channel 
  */
  sConfig.Channel = ADC_CHANNEL_1;
  sConfig.Rank = ADC_REGULAR_RANK_1;
  sConfig.SamplingTime = ADC_SAMPLETIME_1CYCLE_5;
  if (HAL_ADC_ConfigChannel(&hadc2, &sConfig) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN ADC2_Init 2 */

  /* USER CODE END ADC2_Init 2 */

}

/**
  * @brief I2C1 Initialization Function
  * @param None
  * @retval None
  */
static void MX_I2C1_Init(void)
{

  /* USER CODE BEGIN I2C1_Init 0 */

  /* USER CODE END I2C1_Init 0 */

  /* USER CODE BEGIN I2C1_Init 1 */

  /* USER CODE END I2C1_Init 1 */
  hi2c1.Instance = I2C1;
  hi2c1.Init.ClockSpeed = 400000;
  hi2c1.Init.DutyCycle = I2C_DUTYCYCLE_2;
  hi2c1.Init.OwnAddress1 = 0;
  hi2c1.Init.AddressingMode = I2C_ADDRESSINGMODE_7BIT;
  hi2c1.Init.DualAddressMode = I2C_DUALADDRESS_DISABLE;
  hi2c1.Init.OwnAddress2 = 0;
  hi2c1.Init.GeneralCallMode = I2C_GENERALCALL_DISABLE;
  hi2c1.Init.NoStretchMode = I2C_NOSTRETCH_DISABLE;
  if (HAL_I2C_Init(&hi2c1) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN I2C1_Init 2 */

  /* USER CODE END I2C1_Init 2 */

}

/**
  * @brief SPI2 Initialization Function
  * @param None
  * @retval None
  */
static void MX_SPI2_Init(void)
{

  /* USER CODE BEGIN SPI2_Init 0 */

  /* USER CODE END SPI2_Init 0 */

  /* USER CODE BEGIN SPI2_Init 1 */

  /* USER CODE END SPI2_Init 1 */
  /* SPI2 parameter configuration*/
  hspi2.Instance = SPI2;
  hspi2.Init.Mode = SPI_MODE_MASTER;
  hspi2.Init.Direction = SPI_DIRECTION_2LINES;
  hspi2.Init.DataSize = SPI_DATASIZE_8BIT;
  hspi2.Init.CLKPolarity = SPI_POLARITY_LOW;
  hspi2.Init.CLKPhase = SPI_PHASE_2EDGE;
  hspi2.Init.NSS = SPI_NSS_SOFT;
  hspi2.Init.BaudRatePrescaler = SPI_BAUDRATEPRESCALER_16;
  hspi2.Init.FirstBit = SPI_FIRSTBIT_MSB;
  hspi2.Init.TIMode = SPI_TIMODE_DISABLE;
  hspi2.Init.CRCCalculation = SPI_CRCCALCULATION_DISABLE;
  hspi2.Init.CRCPolynomial = 10;
  if (HAL_SPI_Init(&hspi2) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN SPI2_Init 2 */

  /* USER CODE END SPI2_Init 2 */

}

/**
  * @brief TIM3 Initialization Function
  * @param None
  * @retval None
  */
static void MX_TIM3_Init(void)
{

  /* USER CODE BEGIN TIM3_Init 0 */

  /* USER CODE END TIM3_Init 0 */

  TIM_ClockConfigTypeDef sClockSourceConfig = {0};
  TIM_MasterConfigTypeDef sMasterConfig = {0};

  /* USER CODE BEGIN TIM3_Init 1 */

  /* USER CODE END TIM3_Init 1 */
  htim3.Instance = TIM3;
  htim3.Init.Prescaler = 1;
  htim3.Init.CounterMode = TIM_COUNTERMODE_UP;
  htim3.Init.Period = 1656;
  htim3.Init.ClockDivision = TIM_CLOCKDIVISION_DIV1;
  htim3.Init.AutoReloadPreload = TIM_AUTORELOAD_PRELOAD_DISABLE;
  if (HAL_TIM_Base_Init(&htim3) != HAL_OK)
  {
    Error_Handler();
  }
  sClockSourceConfig.ClockSource = TIM_CLOCKSOURCE_INTERNAL;
  if (HAL_TIM_ConfigClockSource(&htim3, &sClockSourceConfig) != HAL_OK)
  {
    Error_Handler();
  }
  sMasterConfig.MasterOutputTrigger = TIM_TRGO_RESET;
  sMasterConfig.MasterSlaveMode = TIM_MASTERSLAVEMODE_DISABLE;
  if (HAL_TIMEx_MasterConfigSynchronization(&htim3, &sMasterConfig) != HAL_OK)
  {
    Error_Handler();
  }
  /* USER CODE BEGIN TIM3_Init 2 */

  /* USER CODE END TIM3_Init 2 */

}

/** 
  * Enable DMA controller clock
  */
static void MX_DMA_Init(void) 
{

  /* DMA controller clock enable */
  __HAL_RCC_DMA1_CLK_ENABLE();

  /* DMA interrupt init */
  /* DMA1_Channel5_IRQn interrupt configuration */
  HAL_NVIC_SetPriority(DMA1_Channel5_IRQn, 0, 0);
  HAL_NVIC_EnableIRQ(DMA1_Channel5_IRQn);

}

/**
  * @brief GPIO Initialization Function
  * @param None
  * @retval None
  */
static void MX_GPIO_Init(void)
{
  GPIO_InitTypeDef GPIO_InitStruct = {0};

  /* GPIO Ports Clock Enable */
  __HAL_RCC_GPIOD_CLK_ENABLE();
  __HAL_RCC_GPIOA_CLK_ENABLE();
  __HAL_RCC_GPIOB_CLK_ENABLE();

  /*Configure GPIO pin Output Level */
  HAL_GPIO_WritePin(GPIOA, GPIO_PIN_2, GPIO_PIN_RESET);

  /*Configure GPIO pin Output Level */
  HAL_GPIO_WritePin(GPIOB, GPIO_PIN_0|GPIO_PIN_8|GPIO_PIN_9, GPIO_PIN_RESET);

  /*Configure GPIO pin Output Level */
  HAL_GPIO_WritePin(GPIOB, GPIO_PIN_1, GPIO_PIN_SET);

  /*Configure GPIO pin : PA2 */
  GPIO_InitStruct.Pin = GPIO_PIN_2;
  GPIO_InitStruct.Mode = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(GPIOA, &GPIO_InitStruct);

  /*Configure GPIO pin : PA3 */
  GPIO_InitStruct.Pin = GPIO_PIN_3;
  GPIO_InitStruct.Mode = GPIO_MODE_INPUT;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  HAL_GPIO_Init(GPIOA, &GPIO_InitStruct);

  /*Configure GPIO pins : PB0 PB1 PB9 */
  GPIO_InitStruct.Pin = GPIO_PIN_0|GPIO_PIN_1|GPIO_PIN_9;
  GPIO_InitStruct.Mode = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(GPIOB, &GPIO_InitStruct);

  /*Configure GPIO pins : PB3 PB4 */
  GPIO_InitStruct.Pin = GPIO_PIN_3|GPIO_PIN_4;
  GPIO_InitStruct.Mode = GPIO_MODE_INPUT;
  GPIO_InitStruct.Pull = GPIO_NOPULL;
  HAL_GPIO_Init(GPIOB, &GPIO_InitStruct);

  /*Configure GPIO pin : PB5 */
  GPIO_InitStruct.Pin = GPIO_PIN_5;
  GPIO_InitStruct.Mode = GPIO_MODE_INPUT;
  GPIO_InitStruct.Pull = GPIO_PULLUP;
  HAL_GPIO_Init(GPIOB, &GPIO_InitStruct);

  /*Configure GPIO pin : PB8 */
  GPIO_InitStruct.Pin = GPIO_PIN_8;
  GPIO_InitStruct.Mode = GPIO_MODE_OUTPUT_PP;
  GPIO_InitStruct.Pull = GPIO_PULLDOWN;
  GPIO_InitStruct.Speed = GPIO_SPEED_FREQ_LOW;
  HAL_GPIO_Init(GPIOB, &GPIO_InitStruct);

}

/* USER CODE BEGIN 4 */
int checkbuttons(void){ // BTN3 = PB5 needs internal Pullups enabled
int c = 0;
c |= HAL_GPIO_ReadPin(GPIOB,GPIO_PIN_5)<<2 | HAL_GPIO_ReadPin(GPIOB,GPIO_PIN_4)<<1 | HAL_GPIO_ReadPin(GPIOB,GPIO_PIN_3);
return c;
}

int checkUSBConnected(void){ // Check for USB is plugged in to power
	int c = 0;
	c=HAL_GPIO_ReadPin(GPIOA,GPIO_PIN_3);
	return c;
}

void USBdataEnable(int c){ //this function will enable USB serial device if VBUS is connected
	if(c){
	HAL_GPIO_WritePin(GPIOB,GPIO_PIN_9, GPIO_PIN_SET);//pull USB Data+ (DP) High
	}else{
		HAL_GPIO_WritePin(GPIOB,GPIO_PIN_9, GPIO_PIN_RESET);//pull USB Data+ (DP) LOW
	}
}

////////////////////////////////////////////////////////////////////////////////START FFt Lib functions
void ComputeFFT(double *vReal, double *vImag, uint16_t samples, uint8_t power, uint8_t dir)
{	// Computes in-place complex-to-complex FFT
	// Reverse bits
	uint16_t j = 0;
	for (uint16_t i = 0; i < (samples - 1); i++) {
		if (i < j) {
			Swap(&vReal[i], &vReal[j]);
			if(dir==FFT_REVERSE)
				Swap(&vImag[i], &vImag[j]);
		}
		uint16_t k = (samples >> 1);
		while (k <= j) {
			j -= k;
			k >>= 1;
		}
		j += k;
	}
	// Compute the FFT
	double c1 = -1.0;
	double c2 = 0.0;
	uint16_t l2 = 1;
	for (uint8_t l = 0; (l < power); l++) {
		uint16_t l1 = l2;
		l2 <<= 1;
		double u1 = 1.0;
		double u2 = 0.0;
		for (j = 0; j < l1; j++) {
			 for (uint16_t i = j; i < samples; i += l2) {
					uint16_t i1 = i + l1;
					double t1 = u1 * vReal[i1] - u2 * vImag[i1];
					double t2 = u1 * vImag[i1] + u2 * vReal[i1];
					vReal[i1] = vReal[i] - t1;
					vImag[i1] = vImag[i] - t2;
					vReal[i] += t1;
					vImag[i] += t2;
			 }
			 double z = ((u1 * c1) - (u2 * c2));
			 u2 = ((u1 * c2) + (u2 * c1));
			 u1 = z;
		}
		c2 = sqrt((1.0 - c1) / 2.0);
		if (dir == FFT_FORWARD) {
			c2 = -c2;
		}
		c1 = sqrt((1.0 + c1) / 2.0);
	}
	// Scaling for reverse transform
	if (dir != FFT_FORWARD) {
		for (uint16_t i = 0; i < samples; i++) {
			 vReal[i] /= samples;
			 vImag[i] /= samples;
		}
	}
}


void ComplexToMagnitude(double *vReal, double *vImag, uint16_t samples){	// vM is half the size of vReal and vImag
	for (uint16_t i = 0; i < samples; i++) {
		vReal[i] = sqrt(sq(vReal[i]) + sq(vImag[i]));
	}
}


uint8_t Exponent(uint16_t value){
	// Calculates the base 2 logarithm of a value
	uint8_t result = 0;
	while (((value >> result) & 1) != 1) result++;
	return(result);
}

// Private functions

void Swap(double *x, double *y){
	double temp = *x;
	*x = *y;
	*y = temp;
}


void Windowing(double *vData, uint16_t samples, uint8_t windowType, uint8_t dir)
{// Weighing factors are computed once before multiple use of FFT
// The weighing function is symetric; half the weighs are recorded
	double samplesMinusOne = (double)(samples - 1.0);
	for (uint16_t i = 0; i < (samples >> 1); i++) {
		double indexMinusOne = (double) i;
		double ratio = (indexMinusOne / samplesMinusOne);
		double weighingFactor = 1.0;
		// Compute and record weighting factor
		switch (windowType) {
		case FFT_WIN_TYP_RECTANGLE: // rectangle (box car)
			weighingFactor = 1.0;
			break;
		case FFT_WIN_TYP_HAMMING: // hamming
			weighingFactor = 0.54 - (0.46 * cos(twoPi * ratio));
			break;
		case FFT_WIN_TYP_HANN: // hann
			weighingFactor = 0.54 * (1.0 - cos(twoPi * ratio));
			break;
		case FFT_WIN_TYP_TRIANGLE: // triangle (Bartlett)
			weighingFactor = 1.0 - ((2.0 * abs(indexMinusOne - (samplesMinusOne / 2.0))) / samplesMinusOne);
			break;
		case FFT_WIN_TYP_NUTTALL: // nuttall
			weighingFactor = 0.355768 - (0.487396 * (cos(twoPi * ratio))) + (0.144232 * (cos(fourPi * ratio))) - (0.012604 * (cos(sixPi * ratio)));
			break;
		case FFT_WIN_TYP_BLACKMAN: // blackman
			weighingFactor = 0.42323 - (0.49755 * (cos(twoPi * ratio))) + (0.07922 * (cos(fourPi * ratio)));
			break;
		case FFT_WIN_TYP_BLACKMAN_NUTTALL: // blackman nuttall
			weighingFactor = 0.3635819 - (0.4891775 * (cos(twoPi * ratio))) + (0.1365995 * (cos(fourPi * ratio))) - (0.0106411 * (cos(sixPi * ratio)));
			break;
		case FFT_WIN_TYP_BLACKMAN_HARRIS: // blackman harris
			weighingFactor = 0.35875 - (0.48829 * (cos(twoPi * ratio))) + (0.14128 * (cos(fourPi * ratio))) - (0.01168 * (cos(sixPi * ratio)));
			break;
		case FFT_WIN_TYP_FLT_TOP: // flat top
			weighingFactor = 0.2810639 - (0.5208972 * cos(twoPi * ratio)) + (0.1980399 * cos(fourPi * ratio));
			break;
		case FFT_WIN_TYP_WELCH: // welch
			weighingFactor = 1.0 - sq((indexMinusOne - samplesMinusOne / 2.0) / (samplesMinusOne / 2.0));
			break;
		}
		if (dir == FFT_FORWARD) {
			vData[i] *= weighingFactor;
			vData[samples - (i + 1)] *= weighingFactor;
		}
		else {
			vData[i] /= weighingFactor;
			vData[samples - (i + 1)] /= weighingFactor;
		}
	}
}



double sq(double x){ //math squaring function
return 	x*x;
}



uint16_t read_adc(){ //reads ADC0 into adcVAL (12-bit?)
    //HAL_ADC_Start(&hadc1);
    uint16_t adcVal = HAL_ADC_GetValue(&hadc1);
	//HAL_ADC_Stop(&hadc1);
	return adcVal;
}
////////////////////////////////////////////////////////////////////////////////END FFt Lib functions


uint16_t read_bat_adc(){ //reads ADC0 into adcVAL (12-bit?)
  HAL_GPIO_WritePin(GPIOA,GPIO_PIN_2, GPIO_PIN_SET);//Battery Check Enabled
  HAL_Delay(10);
  //HAL_ADC_Start(&hadc2);
  uint16_t adcBatVal = HAL_ADC_GetValue(&hadc2);
 // HAL_ADC_Stop(&hadc2);
  HAL_GPIO_WritePin(GPIOA,GPIO_PIN_2, GPIO_PIN_RESET);//Battery Check Disabled
return adcBatVal;
}



void graphMAG() { //draws FFT magnitudes on OLED and RGB Matrix
	  uint8_t slide = 2; //bin number from bin[0] //MAG[0] and MAG[1] are a bitch. starts at MAG[2].
	  uint8_t Sc = 4;//every other bin. 64 bins. 32 usable bins. displaying 16 bins.
  uint16_t freqScale[16]={1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024}; //these set the upper limit (10Bit)
  //adjustVals(); //
  for(int i=0; i<N; i++){
	  MAG[i] = sqrt(REX[i]*REX[i] + IMX[i]*IMX[i]); //Magnitude from Pythagoram of Real and Complex
  	  if (MAG[i] < 0) MAG[i] = 0;
  	  if (MAG[i] > 1023) MAG[i] = 1023;
  }
  for(int k=0; k<16; k++) SSD1306_DrawFilledRectangle(8*k, (SSD1306_HEIGHT-1)-(uint16_t) map(MAG[(k*Sc)+slide],0,freqScale[k],0,(SSD1306_HEIGHT-1)), 6, (uint16_t) map(MAG[(k*Sc)+slide],0,freqScale[k],0,(SSD1306_HEIGHT-1)), 1); //draw 16 bars abs(x[k]) on (0 to k/2)
  SSD1306_UpdateScreen(); //display
  SSD1306_Clear();

  BlankScreen(BLACK);
  for(int x=0; x<8; x++){ //graph on rgb glasses
	  getrand(randSelect);
	  for(int y=0; y<(uint16_t) map(MAG[(x*Sc)+slide],0,1024,0,numRows); y++) setPixelColor(ColumnArray[x][y], Forecolor);   //I changed this to work with the 168 led display(21 cols) and 32 (64/2 usable) Bins
	  for(int y=0; y<(uint16_t) map(MAG[((x+8)*Sc)+slide],0,1024,0,numRows); y++) setPixelColor(ColumnArray[x+13][y], Forecolor);
  }
  show();

}





//AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA Audio Adjustments

void updateLowHighThresh(){ //maybe use these to change mic from Bass, Mids, Highs. instead of
	//Seem like the CENTER channels are the most sensitive. so need them to cancel out fist. But also have the issue with bass traveling the furthest
	//Constant Coefficient to apply to each channel //lower number means LESS Sensitive, more of that freq is needed
	//float ChnlCoef[] = {3.2, 3.6 , 3.8, 4.0, 3.4, 5.5, 5.0}; //heavy base
	//uint32_t ChnlCoef[] = {3.2, 3.6 , 3.8, 4.0, 3.4, 5.5, 5.0}; //NEED 64
	for(int k=0; k<N; k++){ //Change the lowThresh[x] value here
		//lowThresh[k] = (uint32_t) pow(10, micLevel/ChnlCoef[k])  - 1; ////F(x) = 10^(x/ChnlCoef)
		//lowThresh[k] = (uint16_t) (0.15*k)+4;
		//lowThresh[k] = (uint16_t) ((0.9*k-14)*(0.9*k-14))+40; //parabula to make lowthresh high(250ish) on the low MAG[0] and high MAG[32].
		//lowThresh[k] = (uint16_t) ((0.7*k-14)*(0.7*k-14))+40; //parabola to make lowthresh high(250ish) on the low MAG[0] and high MAG[32].
		lowThresh[k]=10;
		//lowThresh[0]=410;
		//lowThresh[1]=410;
		//lowThresh[2]=300;
		//lowThresh[3]=50;
		highThresh[k]=lowThresh[k]+hOffset; //reset the highThresh value to lowthresh + hOffset. Max 255 //Must increase in another function
	}
}


void adjustVals(){ //takes the raw Mic readings (Freqval[]) and removes the noise and lowThresh offsets
	  // Loop for each magnitude and find the magnitiude. not really needed to sqrt
	  for (int i = 0; i < N; i++){
		  MAG[i] = sqrt(REX[i]*REX[i] + IMX[i]*IMX[i]); //Magnitude from Pythagoram of Real and Complex
		  MAG[i] -=lowThresh[i]; // subtract off lowThresh to reduce the value (shift down) MAG[i]
		  if (MAG[i] < 0) MAG[i] = 0;
		  if (MAG[i] > 1023-hOffset) MAG[i] = 1023-hOffset;
		  if (MAG[i] > highThresh[i] && MAG[i] < highThresh[i] + (hOffset*2))  highThresh[i] = MAG[i]+hOffset;//increase highThresh as needed. //uses window that may have flaws

	}
}

//yDist = audioMap(c,numRows,1); // valS[x] proportional to nLength

uint16_t audioMap(int audioIndx, int outHigh, int offsetHigh){//maps ValS[i] to some number and constrains it to some number-another number
	uint16_t temp = (MAG[audioIndx]*outHigh)/(highThresh[audioIndx]-lowThresh[audioIndx]);
			if(temp>outHigh-offsetHigh) temp = outHigh;
	return temp;
}

//AAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAAA Audio Adjustments


void graphMAG_ADJUSTED() { //draws FFT magnitudes on OLED and RGB Matrix
//yDist = audioMap(c,numRows,1); // valS[x] proportional to nLength
//rDist = audioMap(c,red,0);	 // valS[x] proportional to nLength
//gDist = audioMap(c,green,0);	 // valS[x] proportional to nLength
//bDist = audioMap(c,blue,0);	 // valS[x] proportional to nLength
//uint16_t freqScale[16]={1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024}; //these set the upper limit (10Bit)
  uint8_t slide = 4; //bin number from bin[0] //MAG[0] and MAG[1] are a bitch. starts at MAG[2].
  uint8_t Sc = 2;//every other bin. 64 bins. 32 usable bins. displaying 16 bins.
  adjustVals(); //
  for(int k=0; k<16; k++) SSD1306_DrawFilledRectangle(8*k, (SSD1306_HEIGHT-1)-audioMap((k*Sc)+slide,SSD1306_HEIGHT-1,1), 6, audioMap((k*Sc)+slide,SSD1306_HEIGHT-1,1), 1); //draw 16 bars abs(x[k]) on (0 to k/2)
  SSD1306_UpdateScreen(); //display
  SSD1306_Clear();

  BlankScreen(BLACK);
  for(int x=0; x<8; x++){ //graph on rgb glasses
	  getrand(randSelect);
	  for(uint16_t y=0; y<audioMap((x*Sc)+slide,numRows,1); y++) setPixelColor(ColumnArray[x][y], Forecolor);   //I changed this to work with the 168 led display(21 cols) and 32 (64/2 usable) Bins
	  for(uint16_t y=0; y<audioMap(((x+8)*Sc)+slide,numRows,1); y++) setPixelColor(ColumnArray[x+13][y], Forecolor);
  }
  show();
}






/*
void graphMAG_ADJUSTED() { //draws FFT magnitudes on OLED and RGB Matrix
//yDist = audioMap(c,numRows,1); // valS[x] proportional to nLength
//rDist = audioMap(c,red,0);	 // valS[x] proportional to nLength
//gDist = audioMap(c,green,0);	 // valS[x] proportional to nLength
//bDist = audioMap(c,blue,0);	 // valS[x] proportional to nLength
  uint8_t slide = 0; //bin number from bin[0]
  uint8_t Sc = 2;//every other bin. 64 bins. 32 usable bins. displaying 16 bins.
  uint16_t freqScale[16]={1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024,1024}; //these set the upper limit (10Bit)
  adjustVals(); //
  //for(int k=0; k<16; k++) SSD1306_DrawFilledRectangle(8*k, (SSD1306_HEIGHT-1)-(uint16_t) map(MAG[(k*Sc)+2],0,freqScale[k],0,(SSD1306_HEIGHT-1)), 6, (uint16_t) map(MAG[(k*Sc)+2],0,freqScale[k],0,(SSD1306_HEIGHT-1)), 1); //draw 16 bars abs(x[k]) on (0 to k/2)
  for(int k=0; k<16; k++) SSD1306_DrawFilledRectangle(8*k, (SSD1306_HEIGHT-1)-audioMap((k*Sc)+slide,SSD1306_HEIGHT-1,1), 6, audioMap((k*Sc)+slide,SSD1306_HEIGHT-1,1), 1); //draw 16 bars abs(x[k]) on (0 to k/2)
  SSD1306_UpdateScreen(); //display
  SSD1306_Clear();

  BlankScreen(BLACK);
  for(int x=0; x<8; x++){ //graph on rgb glasses
	  getrand(randSelect);
	  for(int y=0; y<(uint16_t) audioMap((x*Sc)+slide,numRows,1); y++) setPixelColor(ColumnArray[x][y], Forecolor);   //I changed this to work with the 168 led display(21 cols) and 32 (64/2 usable) Bins
	  for(int y=0; y<(uint16_t) audioMap(((x+8)*Sc)+slide,numRows,1); y++) setPixelColor(ColumnArray[x+13][y], Forecolor);
  }
  show();

}
*/

void splash(){
BlankScreen(BLACK);
for(int c=0; c<15; c++){
getrand(1); //random red color
setPixelColor( rand() % (NUMLEDS - 0 + 1) + 0, Forecolor); //add a sprinkle                                 //make sprikle brighntess propotional to the freq amplitude
getrand(2); //random red color
setPixelColor( rand() % (NUMLEDS - 0 + 1) + 0, Forecolor); //add a sprinkle
getrand(3); //random red color
setPixelColor( rand() % (NUMLEDS - 0 + 1) + 0, Forecolor); //add a sprinkle
}
show();
}


void show(void){
HAL_SPI_Transmit_DMA(&hspi2, myData, (NUMLEDS*EXPANDFACTOR)+SPILOWTIME); //Begin SPI - SPI DMA data burst to LEDS
//HAL_Delay(2); //(50 LEDs) 2ms delay to prevent sending data modified after DMA call  - will add if needed
//HAL_Delay(4); //(128 LEDSs) 2ms delay to prevent sending data modified after DMA call
}

void setPixelColor(int pixelNum, uint32_t c){ //pass in a Pixel Number and 32bit Color and map to 9 bytes
	  uint8_t myGRB[3]; //create an array to hold the GRB bytes for one 23bit color
	  for(int x=0; x<3; x++) myGRB[x] = (c >> ((2-x) * 8)) & 0xFF; //extract the green,red,blue from the 32bit and write the 8bit values into myGRB array
	  for(int y=0; y<3; y++){ //this is to index the G,R,B bytes
	    for(int x=0; x<3; x++)  myData[(y*3)+(pixelNum*9)+x] = (bitExpand[myGRB[y]] >> ((2-x) * 8)) & 0xFF; //expand green, red, blue. from 1 byte into 3 bytes each (9 bytes total)
	  }
}

uint32_t getPixelColor(int c){ //receives a Led Number and returns its 32 bit value
	uint8_t myGRB[3];
	uint32_t myExpanedByte[3]; //
	uint8_t i=0; //used to index the bittable
	for(int x=0; x<3; x++) myExpanedByte[x] =  ((uint32_t)myData[(c*9)+(3*x)] << 16) | ((uint32_t)myData[(c*9)+(3*x)+1] <<  8) | (uint32_t) myData[(c*9)+(3*x)+2]; //extract values from myData Array
    for(int x=0; x<3; x++){
	  while(myExpanedByte[x] != bitExpand[i]) i++; //loop until match occurs
	  myGRB[x] = i; //store the index into 3 bytes sized values
	  i=0;
     }
	return ((uint32_t)myGRB[0] << 16) | ((uint32_t)myGRB[1] <<  8 | (uint32_t) myGRB[2]); //return a uint32_t value for the color stored on the led
}



void BlankScreen(uint32_t c) { //quickly set the entire screen one color
  for (int i = 0; i < NUMLEDS; i++) {
    setPixelColor(i, c);
  }
  show();
}


void rotateCCW(uint32_t theta){ //rotates all pixels theta rads counter clockwise //not quite working yet. something with math is wrong. test this in codeblocks?
	int myOffset = 5;
	int myX = 10;
	int myY = 5;
	//move to origin: x-
	for(float i=0; i<=2; i+=.5){
	int myXT = myOffset + (int) ((myX-myOffset)*cos(M_PI*i)-(myY-myOffset)*sin(M_PI*i));
	int myYT = myOffset + (int) ((myX-myOffset)*sin(M_PI*i)+(myY-myOffset)*cos(M_PI*i));
	BlankScreen(0);
	setPixelColor(ColumnArray[myX][myY], 0x0A0000); ///set a pixel green
	show();
	HAL_Delay(1000);
	setPixelColor(ColumnArray[myXT][myYT], 0x000A00);
	show();
	HAL_Delay(1000);
	myX = myXT;
	myY = myYT;
	}
}

//shift right function
void HorizShiftR () {   //Shift columns right 1 palce
  for ( int s = numCols-2; s >= 0; s--) { //read one hind. index COLUMNS
    for (int b = 0; b <= numRows-1; b++) { //read each Led value.  inded the ROWS
      ArrayBuffer[b] = getPixelColor(ColumnArray[s][b]); //store 5 int32s into bufferarray
      setPixelColor(ColumnArray[s + 1][b], ArrayBuffer[b]); //put those stored vals in place one to the right
    }
  }
  show();
}

//shift Left function
void HorizShiftL () {   //Shift columns right 1 palce
  for ( int s = 1; s <= numCols-1; s++) { //read one behind left
    for (int b = 0; b <= numRows-1; b++) { //read each Led value
      ArrayBuffer[b] = getPixelColor(ColumnArray[s][b]); //store 5 int32s into bufferarray
      setPixelColor(ColumnArray[s - 1][b], ArrayBuffer[b]); //put those stored vals in place one to the left
    }
  }
  show();
}

void BlankColumn(int c) {    //wipes the coulmn 0 to clear out jjunk, to get ready for shifting
  for (int w = 0; w <= numRows-1; w++) {
   setPixelColor(ColumnArray[c][w], 0x000000);
  }
}



//Extract characters for Scrolling text
void printStringWithShiftL(char* s, int shift_speed) { //Add Color??
	while (*s != 0) {
		printCharWithShiftL(*s, shift_speed);
		s++;
	}
}

// Put extracted character on Display     // this works very well
void printCharWithShiftL(char c, int shift_speed) {
	enum {TEXTPOS = 1};
	if (c < 32) return; //error check for ascii values less than ASCII  < ' ' (space) = 32 >
	c -= 32; //align the char ascii with the CharTable
	memcpy(mbuffer, &CH[3 * c], 3); //CH + 3*c is same as &CH[3*c] //copy 3 items
	//mBuffer
	getrand(randSelect);
	for (int j = 0; j <= 2; j++) {
		uint8_t b = 0b00000001;
		for (int k = TEXTPOS; k < TEXTPOS+5; k++) {
			if (mbuffer[j]&b) setPixelColor(ColumnArray[numCols-1][(numRows-1)-k], Forecolor);
			b = b << 1;
		}
		show();
		HorizShiftL(); //shift every column one column left (one space between letters)
		BlankColumn(numCols-1);
		HAL_Delay(shift_speed);
	}
	HorizShiftL(); // (one space after word)

}


uint32_t Color(uint8_t g,uint8_t r,uint8_t b){ //receives a G,R, amd B byte then Returns a 32bit int
return ((uint32_t)g << 16) | ((uint32_t)r <<  8 | (uint32_t) b);
}


long map(long x, long in_min, long in_max, long out_min, long out_max) { //Map function
  return (x - in_min) * (out_max - out_min) / (in_max - in_min) + out_min;
}

int randomNum(int myLow, int myHigh){  //return random integer for low to high range
	return  (rand() % (myHigh - myLow + 1)) + myLow;
}




void sine1 (uint32_t delayTime) { //single wave  //Shift columns right 1 palce
  for (int i = 0; i < numRows; i++) { //number here determins "density"
			BlankColumn(0);
			setPixelColor(ColumnArray[0][i], Forecolor);
			HorizShiftR();
			HAL_Delay(delayTime);
  }
  for (int i = 0; i < numRows; i++) { //number here determins "density"
			BlankColumn(0);
			setPixelColor(ColumnArray[0][(numRows-1) - i], Forecolor);
			HorizShiftR();
			HAL_Delay(delayTime);
  }
}


void nGrid(){ //make a snake head pop upin a random spot and move it arround the screen randomly
	//BlankScreen(0);
	int numBalls = randomNum(4,7); //number of balls
	int Limitx = numCols-1; //width
	int Limity = numRows-1;//height
	int Headx[numBalls]; //head postion holder
	int Heady[numBalls]; //head postion holder
	int Dirx[numBalls]; //-1 or 1
	int Diry[numBalls]; //-1 or 1
	int Tailx[numBalls]; //tailx psotion. is not really 'seen'. exists to reduce "flickering"
	int Taily[numBalls]; //taily position
	int myGreen[numBalls];
	int myRed[numBalls];
	int myBlue[numBalls];
	for(int c=0; c<numBalls; c++){ //loop through all arrays to set intials
	  getrand(randSelect);
	  myGreen[c] = green; //n number if random colors
	  myRed[c] = red;
	  myBlue[c] = blue;
	  Headx[c] = randomNum(0,Limitx+1); //pick n number of random x start points
	  Heady[c] = randomNum(0,Limity+1); //pick n number of random y start points
	  if(randomNum(0,2)){
	  Dirx[c] = 1;//pow(-1,random(1,2));
	  Diry[c] = 1;//pow(-1,random(1,2));
	  }else{
	  Dirx[c] = -1;//pow(-1,random(1,2));
	  Diry[c] = -1;//pow(-1,random(1,2));
	  }
	}
    for(int i=0; i<=cycles; i++){
		 //checkbtn3();
		  for(int c=0; c<numBalls; c++){
			   if(Headx[c]==0) Dirx[c]=1;
			   if(Headx[c]==Limitx) Dirx[c]=-1;
			   if(Heady[c]==0) Diry[c]=1;
			   if(Heady[c]==Limity) Diry[c]=-1;

			  Tailx[c] = Headx[c];
			  Taily[c] = Heady[c];
			  if(c%2==0){
			  Headx[c]+=Dirx[c];
			  }else{
			  Heady[c]+=Diry[c];
			  }
			  setPixelColor(ColumnArray[Headx[c]][Heady[c]],Color(myGreen[c]/(numBalls-c),myRed[c]/(numBalls-c),myBlue[c]/(numBalls-c))); //set the pixel
			  setPixelColor(ColumnArray[Tailx[c]][Taily[c]],0); //clear the pixel (causing flashing?
		}
		    show();
		 	HAL_Delay(waittime);
	}
	if(randomNum(0,1000)==500){
	printStringWithShiftL(" STARIOS", 40); //Send Lscrolling Text (send car array)
	}

}



void nBalls(){ //make a snake head pop upin a random spot and move it around the screen randomly
	//rand usage: int myRandomnumber = (rand() % (MAX - MIN + 1)) + MIN;
#define MAXBALLS 20
#define MINBALLS 8
	int numBalls = (rand() % (MAXBALLS - MINBALLS + 1)) + MINBALLS; //number of balls
	//int Limitx = (numCols-1); //width
	//int Limity = (numRows-1);//height
	int Headx[numBalls]; //head potion holder
	int Heady[numBalls]; //head postion holder
	int Dirx[numBalls]; //-1 or 1
	int Diry[numBalls]; //-1 or 1
	int Tailx[numBalls]; //tailx position. is not really 'seen'. exists to reduce "flickering"
	int Taily[numBalls]; //taily position
	int myGreen[numBalls];
	int myRed[numBalls];
	int myBlue[numBalls];
	for(int c=0; c<numBalls; c++){ //loop through all arrays to set intials
	  getrand(randSelect);
	  myGreen[c] = green; //n number if random colors
	  myRed[c] = red;
	  myBlue[c] = blue;
	  Headx[c] = (rand() % ((numCols-1) - 0 + 1)) + 0; //pick n number of random x start points //could be replaced using my randomNum function
	  Heady[c] = (rand() % ((numRows-1) - 0 + 1)) + 0; //pick n number of random y start points
	  Dirx[c] = 1;//pow(-1,random(1,2));
	  Diry[c] = 1;//pow(-1,random(1,2));
	}
    for(int i=0; i<=cycles; i++){
		 //checkbtn3();
		  for(int c=0; c<numBalls; c++){
			  if(Headx[c]==0) Dirx[c]=1;
			  if(Headx[c]==(numCols-1)) Dirx[c]=-1;
			  if(Heady[c]==0) Diry[c]=1;
			  if(Heady[c]==(numRows-1)) Diry[c]=-1;

			  Tailx[c] = Headx[c];
			  Taily[c] = Heady[c];
			  Headx[c]+=Dirx[c];
			  Heady[c]+=Diry[c];
			  setPixelColor(ColumnArray[Headx[c]][Heady[c]],Color(myGreen[c],myRed[c],myBlue[c])); //set the pixel
			  setPixelColor(ColumnArray[Tailx[c]][Taily[c]],0); //clear the pixel (causing flashing?
		  }
		  show();
		  HAL_Delay(waittime);
		   if((rand() % (30 - 0 + 1)) + 0 == 15){ //get a random number after all the balls have been updated
			 for(int x=0; x<numBalls; x++){ //loop through each ball
			  getrand(randSelect);
			  myGreen[x] = green; //n number if random colors
			  myRed[x] = red;
			  myBlue[x] = blue;
			  if(Headx[x]<numCols-2 && Headx[x]>=2){
				 for(int z=0; z<numBalls; z++) setPixelColor(ColumnArray[Headx[x]][Heady[x]],0); //needed to clear the stuck balls
				 if((rand() % (2 - 0 + 1)) + 0){ //add a shift to keep things from repeating too much
					 Tailx[x] = Headx[x];
					 Headx[x]++;
				 }else{
					 Tailx[x] = Headx[x];
					 Headx[x]--;
				 }
			  }
			 }
		}
	}
	for(uint8_t k=0; k<16; k++){ //picked 5 times as random amount should be enough to get all to zero
	//instead of setting the color to 0, fade it to 0. need to get the rgb for each color in the array. int32 to 3 byte
	int decayRate = 4; //used to set the speed of the dimming effect
	for(uint8_t j=0; j<numBalls; j++){
	    myRed[j]-=decayRate;
		myGreen[j]-=decayRate;
		myBlue[j]-=decayRate;
		if(myRed[j]<decayRate)myRed[j]=0;
		if(myGreen[j]<decayRate)myGreen[j]=0;
		if(myBlue[j]<decayRate)myBlue[j]=0;
		setPixelColor(ColumnArray[Headx[j]][Heady[j]],Color(myRed[j],myGreen[j],myBlue[j])); //clear the pixels this way insteadof BlankScreen
		show();
		//HAL_Delay(1);
	 }


	}
	if(rand() % (10 - 0 + 1) + 0==5){
	getrand(randSelect);
	BlankScreen(Forecolor);
	}

}








void getrand(int c) { // trying to make it //the goal is to get a random forecolor that is not white, then find the opposite of
  //rand usage: int myRandomnumber = (rand() % (MAX - MIN + 1)) + MIN;
	//getrand requries 0,1,2,3, or specify what type of color to return
      switch ((rand() % (2 - 0 + 1)) + 0) { //0 to 3 //map(rand(),0,32767,0,2)      //could be replaced using my randomNum function
        case 0:                                 //multi
            green = (uint8_t) 2*((rand() % ((Brange+1) - (1) + 1)) + 0);
            red = (uint8_t) 2*((rand() % ((Brange+1) - (0) + 1)) + 0);
            blue = 0;
            if(green==0 && red==0) green = 1;
          break;

        case 1:
        	 green = (uint8_t) 2*((rand() % ((Brange+1) - (0) + 1)) + 0);
        	 blue = (uint8_t) 2*((rand() % ((Brange+1) - (1) + 1)) + 0);
        	 red = 0;
        	 if(green==0 && blue==0) blue = 1;
          break;

        case 2:
        	 blue = (uint8_t) 2*((rand() % ((Brange+1) - (0) + 1)) + 0);
        	 red = (uint8_t) 2*((rand() % ((Brange+1) - (1) + 1)) + 0);
        	 green = 0;
        	 if(blue==0 && red==0) red = 1;
          break;
      }

  Forecolor = ((uint32_t)green << 16) | ((uint32_t)red <<  8) | ((uint32_t)blue);
  //CDC_Transmit_FS(Forecolor, 4); //prints color value to USB virtual serial port



}


/* USER CODE END 4 */

/**
  * @brief  This function is executed in case of error occurrence.
  * @retval None
  */
void Error_Handler(void)
{
  /* USER CODE BEGIN Error_Handler_Debug */
  /* User can add his own implementation to report the HAL error return state */

  /* USER CODE END Error_Handler_Debug */
}

#ifdef  USE_FULL_ASSERT
/**
  * @brief  Reports the name of the source file and the source line number
  *         where the assert_param error has occurred.
  * @param  file: pointer to the source file name
  * @param  line: assert_param error line source number
  * @retval None
  */
void assert_failed(uint8_t *file, uint32_t line)
{ 
  /* USER CODE BEGIN 6 */
  /* User can add his own implementation to report the file name and line number,
     tex: printf("Wrong parameters value: file %s on line %d\r\n", file, line) */
  /* USER CODE END 6 */
}
#endif /* USE_FULL_ASSERT */

/************************ (C) COPYRIGHT STMicroelectronics *****END OF FILE****/
