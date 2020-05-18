################################################################################
# Automatically-generated file. Do not edit!
################################################################################

-include ../makefile.init

RM := rm -rf

# All of the sources participating in the build are defined here
-include sources.mk
-include Startup/subdir.mk
-include Src/subdir.mk
-include Middlewares/ST/STM32_USB_Device_Library/Core/Src/subdir.mk
-include Middlewares/ST/STM32_USB_Device_Library/Class/CDC/Src/subdir.mk
-include Drivers/STM32F1xx_HAL_Driver/Src/subdir.mk
-include subdir.mk
-include objects.mk

ifneq ($(MAKECMDGOALS),clean)
ifneq ($(strip $(C_DEPS)),)
-include $(C_DEPS)
endif
endif

-include ../makefile.defs

# Add inputs and outputs from these tool invocations to the build variables 
EXECUTABLES += \
Starios_2020_ALPHA.elf \

SIZE_OUTPUT += \
default.size.stdout \

OBJDUMP_LIST += \
Starios_2020_ALPHA.list \

OBJCOPY_BIN += \
Starios_2020_ALPHA.bin \


# All Target
all: Starios_2020_ALPHA.elf secondary-outputs

# Tool invocations
Starios_2020_ALPHA.elf: $(OBJS) $(USER_OBJS) C:\Users\Tower\Documents\STM32CubeIDE\workspace_1.0.1\Starios_2020_ALPHA\STM32F103C8TX_FLASH.ld
	arm-none-eabi-gcc -o "Starios_2020_ALPHA.elf" @"objects.list" $(USER_OBJS) $(LIBS) -mcpu=cortex-m3 -T"C:\Users\Tower\Documents\STM32CubeIDE\workspace_1.0.1\Starios_2020_ALPHA\STM32F103C8TX_FLASH.ld" --specs=nosys.specs -Wl,-Map="Starios_2020_ALPHA.map" -Wl,--gc-sections -static -u _printf_float --specs=nano.specs -mfloat-abi=soft -mthumb -Wl,--start-group -lc -lm -Wl,--end-group
	@echo 'Finished building target: $@'
	@echo ' '

default.size.stdout: $(EXECUTABLES)
	arm-none-eabi-size  $(EXECUTABLES)
	@echo 'Finished building: $@'
	@echo ' '

Starios_2020_ALPHA.list: $(EXECUTABLES)
	arm-none-eabi-objdump -h -S $(EXECUTABLES) > "Starios_2020_ALPHA.list"
	@echo 'Finished building: $@'
	@echo ' '

Starios_2020_ALPHA.bin: $(EXECUTABLES)
	arm-none-eabi-objcopy  -O binary $(EXECUTABLES) "Starios_2020_ALPHA.bin"
	@echo 'Finished building: $@'
	@echo ' '

# Other Targets
clean:
	-$(RM) *
	-@echo ' '

secondary-outputs: $(SIZE_OUTPUT) $(OBJDUMP_LIST) $(OBJCOPY_BIN)

.PHONY: all clean dependents
.SECONDARY:

-include ../makefile.targets
