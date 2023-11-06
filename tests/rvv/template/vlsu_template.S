#define VLOAD_V_e32(op) \
   	li		a5, 0                   ; \
    la      a6, initial_data        ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, e32, m1, ta, mu ; \
	vmv.v.x	v24, a5                 ; \
	vmv.v.x	v25, a1                 ; \
    op      v30, (a6)               ; \
	addw	a5, a4, a5              ; \
    addw    a6, a4, a6              ; \
	ble	    a5, a2, 1b
