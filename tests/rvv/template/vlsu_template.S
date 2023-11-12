#define VLOAD_V(op, eew, eew_width) \
   	li		a5, 0                   ; \
    la      a6, initial_data        ; \
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


#define VSTORE_V(op, eew, eew_width) \
   	li		a5, 0                   ; \
    la      a6, initial_data        ; \
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
