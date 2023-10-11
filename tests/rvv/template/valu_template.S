#define VALU_VV(op, sew) \
   	li		a5, 0                   ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, sew, m1, ta, mu ; \
	vmv.v.x	v24, a5                 ; \
	vmv.v.x	v25, a1                 ; \
    op.vv   v30, v24, v25           ; \
	addw	a5, a4, a5              ; \
	ble	    a5, a2, 1b              ; \


#define VALU_VX(op, sew) \
   	li		a5, 0                   ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, sew, m1, ta, mu ; \
	vmv.v.x	v24, a5                 ; \
    op.vx   v30, v24, a1            ; \
	addw	a5, a4, a5              ; \
	ble	    a5, a2, 1b              ; \


#define VALU_VI(op, sew) \
   	li		a5, 0                   ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, sew, m1, ta, mu ; \
	vmv.v.x	v24, a5                 ; \
    op.vi   v30, v24, 0x0a          ; \
	addw	a5, a4, a5              ; \
	ble	    a5, a2, 1b
