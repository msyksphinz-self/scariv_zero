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

#define VALU_MM(op, sew) \
   	li		a5, 0                   ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, sew, m1, ta, mu ; \
	vmv.v.x	v24, a5                 ; \
	vmv.v.x	v25, a1                 ; \
    op.mm   v30, v24, v25           ; \
	addw	a5, a4, a5              ; \
	ble	    a5, a2, 1b

#define VFPU_VV_e32(op) \
   	li		a5, 0                   ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, e32, m1, ta, mu ; \
    fcvt.s.w    f10, a5             ; \
	vfmv.v.f	v24, f10            ; \
    fcvt.s.w    f10, a1             ; \
	vfmv.v.f	v25, f10            ; \
    op.vv   v30, v24, v25           ; \
	addw	a5, a4, a5              ; \
	ble	    a5, a2, 1b

#define VFPU_VV_e64(op) \
   	li		a5, 0                   ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, e64, m1, ta, mu ; \
    fcvt.d.w    f10, a5             ; \
	vfmv.v.f	v24, f10            ; \
    fcvt.d.w    f10, a1             ; \
	vfmv.v.f	v25, f10            ; \
    op.vv   v30, v24, v25           ; \
	addw	a5, a4, a5              ; \
	ble	    a5, a2, 1b

#define VFPU_VVV_e32(op) \
   	li		a5, 1                   ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
	vsetvli	a4, a4, e32, m1, ta, mu ; \
    vmv.v.x v30, x0                 ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, e32, m1, ta, mu ; \
    fcvt.s.w    f10, a5             ; \
	vfmv.v.f	v24, f10            ; \
    fcvt.s.w    f10, a1             ; \
	vfmv.v.f	v25, f10            ; \
    op.vv   v30, v24, v25           ; \
	addw	a5, a4, a5              ; \
	ble	    a5, a2, 1b

#define VFPU_VVV_e64(op) \
   	li		a5, 0                   ; \
	li		a1, 100                 ; \
	li		a2, 99                  ; \
	vsetvli	a4, a4, e64, m1, ta, mu ; \
    vmv.v.x v30, x0                 ; \
1:                                  ; \
	subw	a4, a1, a5              ; \
	vsetvli	a4, a4, e64, m1, ta, mu ; \
    fcvt.d.w    f10, a5             ; \
	vfmv.v.f	v24, f10            ; \
    fcvt.d.w    f10, a1             ; \
	vfmv.v.f	v25, f10            ; \
    op.vv   v30, v24, v25           ; \
	addw	a5, a4, a5              ; \
	ble	    a5, a2, 1b
