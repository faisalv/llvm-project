; NOTE: Assertions have been autogenerated by utils/update_test_checks.py UTC_ARGS: --version 5
; RUN: opt -passes=instcombine -S %s -o - | FileCheck %s
;; Tests that when InstCombine replaces a bswap idiom with an intrinsic, the
;; !dbg attachment from the replaced instruction is applied to all generated
;; instructions, not just the last.

target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-i128:128-f80:128-n8:16:32:64-S128"
target triple = "x86_64-unknown-linux-gnu"

define i32 @inflate(ptr %strm) {
; CHECK-LABEL: define i32 @inflate(
; CHECK-SAME: ptr [[STRM:%.*]]) {
; CHECK-NEXT:  [[ENTRY:.*:]]
; CHECK-NEXT:    [[TMP0:%.*]] = load i64, ptr [[STRM]], align 8
; CHECK-NEXT:    [[TRUNC:%.*]] = trunc i64 [[TMP0]] to i32, !dbg [[DBG3:![0-9]+]]
; CHECK-NEXT:    [[TMP1:%.*]] = and i32 [[TRUNC]], 65535, !dbg [[DBG3]]
; CHECK-NEXT:    [[MASK:%.*]] = call i32 @llvm.bswap.i32(i32 [[TMP1]]), !dbg [[DBG3]]
; CHECK-NEXT:    [[ADD665:%.*]] = zext i32 [[MASK]] to i64, !dbg [[DBG3]]
; CHECK-NEXT:    store i64 [[ADD665]], ptr [[STRM]], align 8
; CHECK-NEXT:    ret i32 0
;
entry:
  %0 = load i64, ptr %strm, align 8
  %and660 = and i64 %0, 65280
  %shl661 = shl i64 %and660, 8
  %and663 = and i64 %0, 255
  %shl664 = shl i64 %and663, 24
  %add665 = or i64 %shl661, %shl664, !dbg !4
  store i64 %add665, ptr %strm, align 8
  ret i32 0
}

!llvm.dbg.cu = !{!0}
!llvm.module.flags = !{!3}

!0 = distinct !DICompileUnit(language: DW_LANG_C11, file: !1, producer: "clang version 20.0.0git")
!1 = !DIFile(filename: "/tmp/zlib_inflate.c", directory: "/tmp")
!2 = !{}
!3 = !{i32 2, !"Debug Info Version", i32 3}
!4 = !DILocation(line: 8, column: 42, scope: !6)
!5 = !DIFile(filename: "zlib_inflate.c", directory: "/tmp")
!6 = distinct !DISubprogram(name: "inflate", scope: !5, file: !5, line: 622, type: !7, scopeLine: 625, unit: !0, retainedNodes: !2)
!7 = distinct !DISubroutineType(types: !2)
;.
; CHECK: [[META0:![0-9]+]] = distinct !DICompileUnit(language: DW_LANG_C11, file: [[META1:![0-9]+]], producer: "{{.*}}clang version {{.*}}", isOptimized: false, runtimeVersion: 0, emissionKind: NoDebug)
; CHECK: [[META1]] = !DIFile(filename: "/tmp/zlib_inflate.c", directory: {{.*}})
; CHECK: [[DBG3]] = !DILocation(line: 8, column: 42, scope: [[META4:![0-9]+]])
; CHECK: [[META4]] = distinct !DISubprogram(name: "inflate", scope: [[META5:![0-9]+]], file: [[META5]], line: 622, type: [[META6:![0-9]+]], scopeLine: 625, spFlags: DISPFlagDefinition, unit: [[META0]], retainedNodes: [[META7:![0-9]+]])
; CHECK: [[META5]] = !DIFile(filename: "zlib_inflate.c", directory: {{.*}})
; CHECK: [[META6]] = distinct !DISubroutineType(types: [[META7]])
; CHECK: [[META7]] = !{}
;.
