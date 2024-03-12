#define E8_WIDTH  (0)
#define E16_WIDTH (1)
#define E32_WIDTH (2)
#define E64_WIDTH (3)

#define VLOAD_V(op, eew, eew_width, data, offset) \
   	li		a5, 0                   ; \
    la      a6, data                ; \
    addi    a6, a6, offset          ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, eew, m1, ta, mu ; \
    op      v30, (a6)               ; \
	add 	a5, a4, a5              ; \
    slli    a7, a4, eew_width       ; \
    add     a6, a7, a6              ; \
	ble	    a5, a2, 1b


#define VSTORE_V(op, eew, eew_width, data) \
   	li		a5, 0                   ; \
    la      a6, data                ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, eew, m1, ta, mu ; \
	vmv.v.x	v30, a5                 ; \
    op      v30, (a6)               ; \
	add 	a5, a4, a5              ; \
    slli    a7, a4, eew_width       ; \
    add     a6, a7, a6              ; \
	ble	    a5, a2, 1b
