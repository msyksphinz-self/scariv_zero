/* Copyright 2019 SiFive, Inc */
/* SPDX-License-Identifier: Apache-2.0 */
/* ----------------------------------- */
/* ----------------------------------- */

#ifndef ASSEMBLY

#include <platform.h>

#ifdef __METAL_MACHINE_MACROS

#ifndef MACROS_IF_SIFIVE_HIFIVE1_REVB____METAL_H
#define MACROS_IF_SIFIVE_HIFIVE1_REVB____METAL_H

#define __METAL_CLINT_NUM_PARENTS 2

#ifndef __METAL_CLINT_NUM_PARENTS
#define __METAL_CLINT_NUM_PARENTS 0
#endif
#define __METAL_PLIC_SUBINTERRUPTS 52

#define __METAL_PLIC_NUM_PARENTS 1

#ifndef __METAL_PLIC_SUBINTERRUPTS
#define __METAL_PLIC_SUBINTERRUPTS 0
#endif
#ifndef __METAL_PLIC_NUM_PARENTS
#define __METAL_PLIC_NUM_PARENTS 0
#endif
#ifndef __METAL_CLIC_SUBINTERRUPTS
#define __METAL_CLIC_SUBINTERRUPTS 0
#endif

#endif /* MACROS_IF_SIFIVE_HIFIVE1_REVB____METAL_H*/

#else /* ! __METAL_MACHINE_MACROS */

#ifndef MACROS_ELSE_SIFIVE_HIFIVE1_REVB____METAL_H
#define MACROS_ELSE_SIFIVE_HIFIVE1_REVB____METAL_H

#define __METAL_CLINT_2000000_INTERRUPTS 2

#define METAL_MAX_CLINT_INTERRUPTS 2

#define __METAL_CLINT_NUM_PARENTS 2

#define __METAL_INTERRUPT_CONTROLLER_C000000_INTERRUPTS 1

#define __METAL_PLIC_SUBINTERRUPTS 52

#define METAL_MAX_PLIC_INTERRUPTS 1

#define __METAL_PLIC_NUM_PARENTS 1

#define __METAL_CLIC_SUBINTERRUPTS 0
#define METAL_MAX_CLIC_INTERRUPTS 0

#define __METAL_LOCAL_EXTERNAL_INTERRUPTS_0_INTERRUPTS 16

#define METAL_MAX_LOCAL_EXT_INTERRUPTS 16

#define METAL_MAX_GLOBAL_EXT_INTERRUPTS 0

#define __METAL_GPIO_10012000_INTERRUPTS 16

#define METAL_MAX_GPIO_INTERRUPTS 16

#define __METAL_SERIAL_10013000_INTERRUPTS 1

#define METAL_MAX_UART_INTERRUPTS 1



// #include <metal/drivers/fixed-clock.h>
// #include <metal/memory.h>
// #include <riscv_clint0.h>
#include <riscv_cpu.h>
// #include <metal/drivers/riscv_plic0.h>
// #include <metal/pmp.h>
// #include <metal/drivers/sifive_local-external-interrupts0.h>
// #include <metal/drivers/sifive_gpio0.h>
// #include <metal/drivers/sifive_gpio-leds.h>
// #include <metal/drivers/sifive_spi0.h>
// #include <metal/drivers/sifive_uart0.h>
// #include <metal/drivers/sifive_fe310-g000_hfrosc.h>
// #include <metal/drivers/sifive_fe310-g000_hfxosc.h>
// #include <metal/drivers/sifive_fe310-g000_pll.h>
// #include <metal/drivers/sifive_fe310-g000_prci.h>

// /* From clock@0 */
// struct __metal_driver_fixed_clock __metal_dt_clock_0;
//
// /* From clock@2 */
// struct __metal_driver_fixed_clock __metal_dt_clock_2;
//
// /* From clock@5 */
// struct __metal_driver_fixed_clock __metal_dt_clock_5;
//
// struct metal_memory __metal_dt_mem_dtim_80000000;
//
// struct metal_memory __metal_dt_mem_spi_10014000;
//
// struct metal_memory __metal_dt_mem_spi_10024000;

/* From clint@2000000 */
// struct __metal_driver_riscv_clint0 __metal_dt_clint_2000000;

// /* From cpu@0 */
// struct __metal_driver_cpu __metal_dt_cpu_0;
//
// struct __metal_driver_riscv_cpu_intc __metal_dt_cpu_0_interrupt_controller;
//
// /* From interrupt_controller@c000000 */
// struct __metal_driver_riscv_plic0 __metal_dt_interrupt_controller_c000000;
//
// struct metal_pmp __metal_dt_pmp;
//
// /* From local_external_interrupts_0 */
// struct __metal_driver_sifive_local_external_interrupts0 __metal_dt_local_external_interrupts_0;
//
// /* From gpio@10012000 */
// struct __metal_driver_sifive_gpio0 __metal_dt_gpio_10012000;
//
// /* From led@0red */
// struct __metal_driver_sifive_gpio_led __metal_dt_led_0red;
//
// /* From led@0green */
// struct __metal_driver_sifive_gpio_led __metal_dt_led_0green;
//
// /* From led@0blue */
// struct __metal_driver_sifive_gpio_led __metal_dt_led_0blue;
//
// /* From spi@10014000 */
// struct __metal_driver_sifive_spi0 __metal_dt_spi_10014000;
//
// /* From spi@10024000 */
// struct __metal_driver_sifive_spi0 __metal_dt_spi_10024000;
//
// /* From serial@10013000 */
// struct __metal_driver_sifive_uart0 __metal_dt_serial_10013000;
//
// /* From serial@10023000 */
// struct __metal_driver_sifive_uart0 __metal_dt_serial_10023000;
//
//
// /* From clock@3 */
// struct __metal_driver_sifive_fe310_g000_hfrosc __metal_dt_clock_3;
//
// /* From clock@1 */
// struct __metal_driver_sifive_fe310_g000_hfxosc __metal_dt_clock_1;
//
// /* From clock@4 */
// struct __metal_driver_sifive_fe310_g000_pll __metal_dt_clock_4;
//
// /* From prci@10008000 */
// struct __metal_driver_sifive_fe310_g000_prci __metal_dt_prci_10008000;


/*!
 * @brief Possible mode of interrupts to operate
 */
typedef enum metal_vector_mode_ {
    METAL_DIRECT_MODE = 0,
    METAL_VECTOR_MODE = 1,
    METAL_SELECTIVE_VECTOR_MODE = 2,
    METAL_HARDWARE_VECTOR_MODE = 3
} metal_vector_mode;

/*!
 * @brief Function signature for interrupt callback handlers
 */
typedef void (*metal_interrupt_handler_t) (int, void *);

struct metal_interrupt;

struct metal_interrupt_vtable {
    void (*interrupt_init)(struct metal_interrupt *controller);
    int (*interrupt_register)(struct metal_interrupt *controller, int id,
			      metal_interrupt_handler_t isr, void *priv_data);
    int (*interrupt_enable)(struct metal_interrupt *controller, int id);
    int (*interrupt_disable)(struct metal_interrupt *controller, int id);
    int (*interrupt_vector_enable)(struct metal_interrupt *controller,
                                   int id, metal_vector_mode mode);
    int (*interrupt_vector_disable)(struct metal_interrupt *controller, int id);
    int (*command_request)(struct metal_interrupt *controller, int cmd, void *data);
    int (*mtimecmp_set)(struct metal_interrupt *controller, int hartid, unsigned long long time);
};

/*!
 * @brief A handle for an interrupt
 */
struct metal_interrupt {
    const struct metal_interrupt_vtable *vtable;
};


/* --------------------- sifive_clint0 ------------ */
// static inline unsigned long __metal_driver_sifive_clint0_control_base(struct metal_interrupt *controller)
// {
// 	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_clint_2000000) {
// 		return METAL_RISCV_CLINT0_2000000_BASE_ADDRESS;
// 	}
// 	else {
// 		return 0;
// 	}
// }
//
// static inline unsigned long __metal_driver_sifive_clint0_control_size(struct metal_interrupt *controller)
// {
// 	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_clint_2000000) {
// 		return METAL_RISCV_CLINT0_2000000_SIZE;
// 	}
// 	else {
// 		return 0;
// 	}
// }
//
// static inline int __metal_driver_sifive_clint0_num_interrupts(struct metal_interrupt *controller)
// {
// 	if ((uintptr_t)controller == (uintptr_t)&__metal_dt_clint_2000000) {
// 		return METAL_MAX_CLINT_INTERRUPTS;
// 	}
// 	else {
// 		return 0;
// 	}
// }

static inline int __metal_driver_sifive_clint0_interrupt_lines(struct metal_interrupt *controller, int idx)
{
	if (idx == 0) {
		return 3;
	}
	else if (idx == 1) {
		return 7;
	}
	else {
		return 0;
	}
}


static inline int __metal_driver_sifive_local_external_interrupts0_interrupt_lines(struct metal_interrupt *controller, int idx)
{
	if (idx == 0) {
		return 16;
	}
	else if (idx == 1) {
		return 17;
	}
	else if (idx == 2) {
		return 18;
	}
	else if (idx == 3) {
		return 19;
	}
	else if (idx == 4) {
		return 20;
	}
	else if (idx == 5) {
		return 21;
	}
	else if (idx == 6) {
		return 22;
	}
	else if (idx == 7) {
		return 23;
	}
	else if (idx == 8) {
		return 24;
	}
	else if (idx == 9) {
		return 25;
	}
	else if (idx == 10) {
		return 26;
	}
	else if (idx == 11) {
		return 27;
	}
	else if (idx == 12) {
		return 28;
	}
	else if (idx == 13) {
		return 29;
	}
	else if (idx == 14) {
		return 30;
	}
	else if (idx == 15) {
		return 31;
	}
	else {
		return 0;
	}
}





#endif /* MACROS_ELSE_SIFIVE_HIFIVE1_REVB____METAL_H*/

#endif /* ! __METAL_MACHINE_MACROS */

#endif /* ! ASSEMBLY */
