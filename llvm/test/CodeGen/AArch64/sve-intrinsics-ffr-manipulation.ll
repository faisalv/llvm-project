; NOTE: Assertions have been autogenerated by utils/update_llc_test_checks.py
; RUN: llc -verify-machineinstrs < %s | FileCheck %s

target triple = "aarch64-unknown-linux-gnu"

;
; RDFFR
;

define <vscale x 16 x i1> @rdffr() #0 {
; CHECK-LABEL: rdffr:
; CHECK:       // %bb.0:
; CHECK-NEXT:    rdffr p0.b
; CHECK-NEXT:    ret
  %out = call <vscale x 16 x i1> @llvm.aarch64.sve.rdffr()
  ret <vscale x 16 x i1> %out
}

define <vscale x 16 x i1> @rdffr_z(<vscale x 16 x i1> %pg) #0 {
; CHECK-LABEL: rdffr_z:
; CHECK:       // %bb.0:
; CHECK-NEXT:    rdffr p0.b, p0/z
; CHECK-NEXT:    ret
  %out = call <vscale x 16 x i1> @llvm.aarch64.sve.rdffr.z(<vscale x 16 x i1> %pg)
  ret <vscale x 16 x i1> %out
}

; Test that rdffr.z followed by ptest optimizes to flags-setting rdffrs.
define i1 @rdffr_z_ptest(<vscale x 16 x i1> %pg) #0 {
; CHECK-LABEL: rdffr_z_ptest:
; CHECK:       // %bb.0:
; CHECK-NEXT:    rdffrs p0.b, p0/z
; CHECK-NEXT:    cset w0, ne
; CHECK-NEXT:    ret
  %rdffr = call <vscale x 16 x i1> @llvm.aarch64.sve.rdffr.z(<vscale x 16 x i1> %pg)
  %out = call i1 @llvm.aarch64.sve.ptest.any.nxv16i1(<vscale x 16 x i1> %pg, <vscale x 16 x i1> %rdffr)
  ret i1 %out
}

;
; SETFFR
;

define void @set_ffr() #0 {
; CHECK-LABEL: set_ffr:
; CHECK:       // %bb.0:
; CHECK-NEXT:    setffr
; CHECK-NEXT:    ret
  call void @llvm.aarch64.sve.setffr()
  ret void
}

;
; WRFFR
;

define void @wrffr(<vscale x 16 x i1> %a) #0 {
; CHECK-LABEL: wrffr:
; CHECK:       // %bb.0:
; CHECK-NEXT:    wrffr p0.b
; CHECK-NEXT:    ret
  call void @llvm.aarch64.sve.wrffr(<vscale x 16 x i1> %a)
  ret void
}

declare <vscale x 16 x i1> @llvm.aarch64.sve.rdffr()
declare <vscale x 16 x i1> @llvm.aarch64.sve.rdffr.z(<vscale x 16 x i1>)
declare void @llvm.aarch64.sve.setffr()
declare void @llvm.aarch64.sve.wrffr(<vscale x 16 x i1>)

declare i1 @llvm.aarch64.sve.ptest.any.nxv16i1(<vscale x 16 x i1>, <vscale x 16 x i1>)

attributes #0 = { "target-features"="+sve" }
