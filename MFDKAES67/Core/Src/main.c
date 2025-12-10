/* USER CODE BEGIN Header */
/**
  ******************************************************************************
  * @file           : main.c
  * @brief          : Main program body
  ******************************************************************************
  * @attention
  *
  * Copyright (c) 2025 STMicroelectronics.
  * All rights reserved.
  *
  * This software is licensed under terms that can be found in the LICENSE file
  * in the root directory of this software component.
  * If no LICENSE file comes with this software, it is provided AS-IS.
  *
  ******************************************************************************
  */
/* USER CODE END Header */
/* Includes ------------------------------------------------------------------*/
#include "main.h"
#include "cmsis_os.h"
#include "lwip.h"

/* Private includes ----------------------------------------------------------*/
/* USER CODE BEGIN Includes */
//#include "lwip/apps/lwiperf.h"
#include "lwip/udp.h"
#include <string.h>
#include <stdint.h>
#include <math.h>
/* USER CODE END Includes */

/* Private typedef -----------------------------------------------------------*/
/* USER CODE BEGIN PTD */

/* USER CODE END PTD */

/* Private define ------------------------------------------------------------*/
/* USER CODE BEGIN PD */

/* USER CODE END PD */

/* Private macro -------------------------------------------------------------*/
/* USER CODE BEGIN PM */

/* USER CODE END PM */

/* Private variables ---------------------------------------------------------*/

/* Definitions for defaultTask */
osThreadId_t defaultTaskHandle;
const osThreadAttr_t defaultTask_attributes = {
  .name = "defaultTask",
  .stack_size = 128 * 4,
  .priority = (osPriority_t) osPriorityNormal,
};
/* USER CODE BEGIN PV */
#define PI 3.14159265358979323846
/* --- Audio / RTP configuration (edit these defines to scale) --- */
#define SAMPLE_RATE         48000U
#define CHANNELS            16U      /* change as needed */
#define BIT_DEPTH           24U      /* bits per sample: 8,16,24,32 supported */
#define FRAME_DURATION_MS   1U       /* frame duration in ms */
#define FRAME_SAMPLES       ((SAMPLE_RATE * FRAME_DURATION_MS) / 1000U)

#define RTP_HEADER_SIZE     12U

/* Network / MTU tuning */
#define ETHERNET_MTU        1500U
#define IP_HEADER_LEN       20U
#define UDP_HEADER_LEN      8U
#define ETHERNET_HEADER_LEN 14U

/* safe UDP payload: slightly below MTU to account for headers */
#define SAFE_UDP_PAYLOAD     (ETHERNET_MTU - IP_HEADER_LEN - UDP_HEADER_LEN - ETHERNET_HEADER_LEN)

/* max payload per RTP fragment */
#define MAX_RTP_PAYLOAD     (SAFE_UDP_PAYLOAD - RTP_HEADER_SIZE)

/* Derived */
#define BYTES_PER_SAMPLE    (((BIT_DEPTH) + 7U) / 8U)
#define FRAME_PAYLOAD_BYTES (FRAME_SAMPLES * CHANNELS * BYTES_PER_SAMPLE)

#if (BYTES_PER_SAMPLE < 1) || (BYTES_PER_SAMPLE > 4)
#error "BYTES_PER_SAMPLE must be 1..4 (BIT_DEPTH 1..32)"
#endif

#define RTP_PAYLOAD_TYPE    96U  /* dynamic payload type */

/* RTP state */
static uint16_t rtp_seq_num = 0;
static uint32_t rtp_timestamp = 0;
static uint32_t rtp_ssrc = 0x12345678;

/* --- Sine tables for different bit depths --- */
//#define SINE_TABLE_SIZE 232

/* Frequencies for each channel (Hz). Edit per-channel freqs here */
static const float channel_freq[CHANNELS] = {
    100.0f, 150.0f, 200.0f, 250.0f,
    300.0f, 350.0f, 400.0f, 450.0f,
    500.0f,  600.0f,  700.0f,  800.0f,
    900.0f, 1000.0f, 2000.0f, 4000.0f
};

/* Phase accumulators and increments sized by CHANNELS */
static uint32_t phase_acc[CHANNELS];
static uint32_t phase_inc[CHANNELS];

/* Transmit scratch buffer for header + max payload per RTP fragment */
static uint8_t rtp_tx_buf[RTP_HEADER_SIZE + MAX_RTP_PAYLOAD];
/* USER CODE END PV */

/* Private function prototypes -----------------------------------------------*/
void SystemClock_Config(void);
static void MPU_Config(void);
static void MX_GPIO_Init(void);
void StartDefaultTask(void *argument);

/* USER CODE BEGIN PFP */

/* USER CODE END PFP */

/* Private user code ---------------------------------------------------------*/
/* USER CODE BEGIN 0 */
/* Initialize phase increments (Q16.16 fixed point) */
static void init_phase_increments(void)
{
    for (unsigned ch = 0; ch < CHANNELS; ++ch) {
        double phase_step = (double)channel_freq[ch] / (double)SAMPLE_RATE; // fraction of full cycle per sample
        phase_inc[ch] = (uint32_t)(phase_step * 65536.0 * 256.0 + 0.5); // scaled for 256-step sine
        phase_acc[ch] = 0;
    }
}


/* Generate FRAME_SAMPLES frames of interleaved samples into int32 container */
static void generate_sine_frame_int32(int32_t *buffer)
{
    for (unsigned i = 0; i < FRAME_SAMPLES; ++i) {
        for (unsigned ch = 0; ch < CHANNELS; ++ch) {
            // Compute phase as 0..1
            double phase = (double)phase_acc[ch] / (65536.0 * 256.0);
            double s = sin(2.0 * PI * phase);

            // Scale to bit depth with rounding
            int32_t sample;
            switch (BIT_DEPTH) {
                case 8:  sample = (int32_t)(s * 127.0 + (s >= 0 ? 0.5 : -0.5)); break;
                case 16: sample = (int32_t)(s * 32767.0 + (s >= 0 ? 0.5 : -0.5)); break;
                case 24: sample = (int32_t)(s * 8388607.0 + (s >= 0 ? 0.5 : -0.5)); break;
                case 32: sample = (int32_t)(s * 2147483647.0 + (s >= 0 ? 0.5 : -0.5)); break;
                default: sample = (int32_t)(s * 32767.0 + (s >= 0 ? 0.5 : -0.5)); break;
            }

            buffer[i * CHANNELS + ch] = sample;

            // advance phase
            phase_acc[ch] += phase_inc[ch];
            if (phase_acc[ch] >= (256 << 16))
                phase_acc[ch] -= (256 << 16);
        }
    }
}

/* Pack int32 samples (interleaved) into big-endian bytes with BYTES_PER_SAMPLE bytes per sample.
   dst length must be (samples_count * BYTES_PER_SAMPLE). */
static void pack_samples_big_endian(const int32_t *src, uint8_t *dst, unsigned samples_count)
{
    uint32_t mask = 0xFFFFFFFFUL;
    if (BYTES_PER_SAMPLE < 4) {
        mask = (1UL << (BYTES_PER_SAMPLE * 8)) - 1UL;
    }

    for (unsigned i = 0; i < samples_count; ++i) {
        uint32_t val = (uint32_t)src[i] & mask;
        /* write MSB first */
        for (int b = (int)BYTES_PER_SAMPLE - 1; b >= 0; --b) {
            dst[i * BYTES_PER_SAMPLE + ((BYTES_PER_SAMPLE - 1) - b)] = (uint8_t)((val >> (8 * b)) & 0xFF);
        }
    }
}

/* Send one RTP datagram (header already in rtp_buf[0..11], payload at rtp_buf+12) */
static void send_rtp_datagram(struct udp_pcb *pcb, const ip_addr_t *dst_ip, u16_t dst_port, uint8_t *rtp_buf, uint16_t payload_len)
{
    uint16_t total_len = RTP_HEADER_SIZE + payload_len;
    struct pbuf *p = pbuf_alloc(PBUF_TRANSPORT, total_len, PBUF_RAM);
    if (!p) {
        /* allocation failed - drop */
        return;
    }

    pbuf_take(p, rtp_buf, total_len);
    udp_sendto(pcb, p, dst_ip, dst_port);
    pbuf_free(p);
}

/* Fragment and send a full frame payload (big-endian packed audio) of length payload_len.
   samples_per_frame is the sample-frame count (used to advance rtp_timestamp once). */
static void send_rtp_frame_fragmented(struct udp_pcb *pcb, const ip_addr_t *dst_ip, u16_t dst_port,
                                      uint8_t *payload_ptr, uint32_t payload_len, uint32_t samples_per_frame)
{
    uint32_t offset = 0;
    uint16_t seq = rtp_seq_num;
    const uint8_t payload_type = (uint8_t)RTP_PAYLOAD_TYPE;

    while (offset < payload_len) {
        uint32_t remaining = payload_len - offset;
        uint16_t chunk = (remaining > MAX_RTP_PAYLOAD) ? (uint16_t)MAX_RTP_PAYLOAD : (uint16_t)remaining;

        // Build RTP header
        rtp_tx_buf[0] = 0x80; // V=2
        // Marker bit set only on last fragment of the frame
        uint8_t marker = ((offset + chunk) >= payload_len) ? 0x80 : 0x00;
        rtp_tx_buf[1] = marker | (payload_type & 0x7F);

        rtp_tx_buf[2] = (uint8_t)(seq >> 8);
        rtp_tx_buf[3] = (uint8_t)(seq & 0xFF);

        rtp_tx_buf[4] = (uint8_t)(rtp_timestamp >> 24);
        rtp_tx_buf[5] = (uint8_t)(rtp_timestamp >> 16);
        rtp_tx_buf[6] = (uint8_t)(rtp_timestamp >> 8);
        rtp_tx_buf[7] = (uint8_t)(rtp_timestamp & 0xFF);

        rtp_tx_buf[8]  = (uint8_t)(rtp_ssrc >> 24);
        rtp_tx_buf[9]  = (uint8_t)(rtp_ssrc >> 16);
        rtp_tx_buf[10] = (uint8_t)(rtp_ssrc >> 8);
        rtp_tx_buf[11] = (uint8_t)(rtp_ssrc & 0xFF);

        // Copy payload chunk
        memcpy(&rtp_tx_buf[RTP_HEADER_SIZE], payload_ptr + offset, chunk);

        // Send RTP packet
        send_rtp_datagram(pcb, dst_ip, dst_port, rtp_tx_buf, chunk);

        offset += chunk;
        seq++;

        // Only advance timestamp on last fragment
        if (offset >= payload_len) {
            rtp_timestamp += samples_per_frame;
        }
    }

    rtp_seq_num = seq;
}
/* USER CODE END 0 */

/**
  * @brief  The application entry point.
  * @retval int
  */
int main(void)
{

  /* USER CODE BEGIN 1 */

  /* USER CODE END 1 */

  /* MPU Configuration--------------------------------------------------------*/
  MPU_Config();

  /* MCU Configuration--------------------------------------------------------*/

  /* Reset of all peripherals, Initializes the Flash interface and the Systick. */
  HAL_Init();

  /* USER CODE BEGIN Init */
  //NVIC_SetPriorityGrouping(0);
  /* USER CODE END Init */

  /* Configure the system clock */
  SystemClock_Config();

  /* USER CODE BEGIN SysInit */

  /* USER CODE END SysInit */

  /* Initialize all configured peripherals */
  MX_GPIO_Init();
  /* USER CODE BEGIN 2 */

  /* USER CODE END 2 */

  /* Init scheduler */
  osKernelInitialize();

  /* USER CODE BEGIN RTOS_MUTEX */
  /* add mutexes, ... */
  /* USER CODE END RTOS_MUTEX */

  /* USER CODE BEGIN RTOS_SEMAPHORES */
  /* add semaphores, ... */
  /* USER CODE END RTOS_SEMAPHORES */

  /* USER CODE BEGIN RTOS_TIMERS */
  /* start timers, add new ones, ... */
  /* USER CODE END RTOS_TIMERS */

  /* USER CODE BEGIN RTOS_QUEUES */
  /* add queues, ... */
  /* USER CODE END RTOS_QUEUES */

  /* Create the thread(s) */
  /* creation of defaultTask */
  defaultTaskHandle = osThreadNew(StartDefaultTask, NULL, &defaultTask_attributes);

  /* USER CODE BEGIN RTOS_THREADS */
  /* add threads, ... */
  /* USER CODE END RTOS_THREADS */

  /* USER CODE BEGIN RTOS_EVENTS */
  /* add events, ... */
  /* USER CODE END RTOS_EVENTS */

  /* Start scheduler */
  osKernelStart();

  /* We should never get here as control is now taken by the scheduler */

  /* Infinite loop */
  /* USER CODE BEGIN WHILE */
  while (1)
  {
    /* USER CODE END WHILE */

    /* USER CODE BEGIN 3 */
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

  /** Supply configuration update enable
  */
  HAL_PWREx_ConfigSupply(PWR_LDO_SUPPLY);

  /** Configure the main internal regulator output voltage
  */
  __HAL_PWR_VOLTAGESCALING_CONFIG(PWR_REGULATOR_VOLTAGE_SCALE3);

  while(!__HAL_PWR_GET_FLAG(PWR_FLAG_VOSRDY)) {}

  /** Initializes the RCC Oscillators according to the specified parameters
  * in the RCC_OscInitTypeDef structure.
  */
  RCC_OscInitStruct.OscillatorType = RCC_OSCILLATORTYPE_HSI;
  RCC_OscInitStruct.HSIState = RCC_HSI_DIV1;
  RCC_OscInitStruct.HSICalibrationValue = RCC_HSICALIBRATION_DEFAULT;
  RCC_OscInitStruct.PLL.PLLState = RCC_PLL_NONE;
  if (HAL_RCC_OscConfig(&RCC_OscInitStruct) != HAL_OK)
  {
    Error_Handler();
  }

  /** Initializes the CPU, AHB and APB buses clocks
  */
  RCC_ClkInitStruct.ClockType = RCC_CLOCKTYPE_HCLK|RCC_CLOCKTYPE_SYSCLK
                              |RCC_CLOCKTYPE_PCLK1|RCC_CLOCKTYPE_PCLK2
                              |RCC_CLOCKTYPE_D3PCLK1|RCC_CLOCKTYPE_D1PCLK1;
  RCC_ClkInitStruct.SYSCLKSource = RCC_SYSCLKSOURCE_HSI;
  RCC_ClkInitStruct.SYSCLKDivider = RCC_SYSCLK_DIV1;
  RCC_ClkInitStruct.AHBCLKDivider = RCC_HCLK_DIV1;
  RCC_ClkInitStruct.APB3CLKDivider = RCC_APB3_DIV1;
  RCC_ClkInitStruct.APB1CLKDivider = RCC_APB1_DIV1;
  RCC_ClkInitStruct.APB2CLKDivider = RCC_APB2_DIV1;
  RCC_ClkInitStruct.APB4CLKDivider = RCC_APB4_DIV1;

  if (HAL_RCC_ClockConfig(&RCC_ClkInitStruct, FLASH_LATENCY_1) != HAL_OK)
  {
    Error_Handler();
  }
}

/**
  * @brief GPIO Initialization Function
  * @param None
  * @retval None
  */
static void MX_GPIO_Init(void)
{
  /* USER CODE BEGIN MX_GPIO_Init_1 */

  /* USER CODE END MX_GPIO_Init_1 */

  /* GPIO Ports Clock Enable */
  __HAL_RCC_GPIOC_CLK_ENABLE();
  __HAL_RCC_GPIOA_CLK_ENABLE();
  __HAL_RCC_GPIOB_CLK_ENABLE();

  /* USER CODE BEGIN MX_GPIO_Init_2 */

  /* USER CODE END MX_GPIO_Init_2 */
}

/* USER CODE BEGIN 4 */

/* USER CODE END 4 */

/* USER CODE BEGIN Header_StartDefaultTask */
/**
  * @brief  Function implementing the defaultTask thread.
  * @param  argument: Not used
  * @retval None
  */
/* USER CODE END Header_StartDefaultTask */
void StartDefaultTask(void *argument)
{
  /* init code for LWIP */
  MX_LWIP_Init();
  /* USER CODE BEGIN 5 */
  osDelay(1000); // Small delay to ensure network initialization

      // --- Setup UDP connection ---
      ip_addr_t dst_ip;
      IP_ADDR4(&dst_ip, 192, 168, 1, 1);
      struct udp_pcb *udp = udp_new();
      if (!udp) {
          for (;;) { osDelay(1000); } // allocation failed
      }
      udp_connect(udp, &dst_ip, 55151);

      /* Prepare buffers */
      static int32_t audio_frame[FRAME_SAMPLES * CHANNELS];       // int32 samples
      uint32_t full_payload_bytes = FRAME_PAYLOAD_BYTES;
      uint8_t *packed_payload = pvPortMalloc(full_payload_bytes);
      if (!packed_payload) {
          for (;;) { osDelay(1000); }
      }

      /* initialize DDS */
      init_phase_increments();
      rtp_ssrc = (uint32_t)HAL_GetTick() ^ 0xA5A5A5A5U;

      const uint32_t frame_interval_ms = FRAME_DURATION_MS;
      uint32_t next_tick = HAL_GetTick();

      /* Main audio streaming loop */
      for (;;) {
          /* Wait until next scheduled tick */
          uint32_t now = HAL_GetTick();
          if ((int32_t)(next_tick - now) > 0) {
              osDelay(next_tick - now);
          }

          next_tick += frame_interval_ms;

          /* Generate interleaved int32 samples */
          generate_sine_frame_int32(audio_frame);

          /* Pack to big-endian bytes */
          pack_samples_big_endian(audio_frame, packed_payload, FRAME_SAMPLES * CHANNELS);

          /* Send (fragments if needed) */
          send_rtp_frame_fragmented(udp, &dst_ip, 55151, packed_payload, full_payload_bytes, FRAME_SAMPLES);
      }

      vPortFree(packed_payload); // never reached
  /* USER CODE END 5 */
}

 /* MPU Configuration */

void MPU_Config(void)
{
  MPU_Region_InitTypeDef MPU_InitStruct = {0};

  /* Disables the MPU */
  HAL_MPU_Disable();

  /** Initializes and configures the Region and the memory to be protected
  */
  MPU_InitStruct.Enable = MPU_REGION_ENABLE;
  MPU_InitStruct.Number = MPU_REGION_NUMBER0;
  MPU_InitStruct.BaseAddress = 0x0;
  MPU_InitStruct.Size = MPU_REGION_SIZE_4GB;
  MPU_InitStruct.SubRegionDisable = 0x87;
  MPU_InitStruct.TypeExtField = MPU_TEX_LEVEL0;
  MPU_InitStruct.AccessPermission = MPU_REGION_NO_ACCESS;
  MPU_InitStruct.DisableExec = MPU_INSTRUCTION_ACCESS_DISABLE;
  MPU_InitStruct.IsShareable = MPU_ACCESS_SHAREABLE;
  MPU_InitStruct.IsCacheable = MPU_ACCESS_NOT_CACHEABLE;
  MPU_InitStruct.IsBufferable = MPU_ACCESS_NOT_BUFFERABLE;

  HAL_MPU_ConfigRegion(&MPU_InitStruct);
  /* Enables the MPU */
  HAL_MPU_Enable(MPU_PRIVILEGED_DEFAULT);

}

/**
  * @brief  Period elapsed callback in non blocking mode
  * @note   This function is called  when TIM6 interrupt took place, inside
  * HAL_TIM_IRQHandler(). It makes a direct call to HAL_IncTick() to increment
  * a global variable "uwTick" used as application time base.
  * @param  htim : TIM handle
  * @retval None
  */
void HAL_TIM_PeriodElapsedCallback(TIM_HandleTypeDef *htim)
{
  /* USER CODE BEGIN Callback 0 */

  /* USER CODE END Callback 0 */
  if (htim->Instance == TIM6)
  {
    HAL_IncTick();
  }
  /* USER CODE BEGIN Callback 1 */

  /* USER CODE END Callback 1 */
}

/**
  * @brief  This function is executed in case of error occurrence.
  * @retval None
  */
void Error_Handler(void)
{
  /* USER CODE BEGIN Error_Handler_Debug */
  /* User can add his own implementation to report the HAL error return state */
  __disable_irq();
  while (1)
  {
  }
  /* USER CODE END Error_Handler_Debug */
}
#ifdef USE_FULL_ASSERT
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
     ex: printf("Wrong parameters value: file %s on line %d\r\n", file, line) */
  /* USER CODE END 6 */
}
#endif /* USE_FULL_ASSERT */
