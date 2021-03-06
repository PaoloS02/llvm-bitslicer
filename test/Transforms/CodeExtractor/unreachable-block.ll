; RUN: opt -S -partial-inliner %s | FileCheck %s

; CHECK-LABEL: define void @dipsy(
; CHECK-NEXT:   call void @tinkywinky.1_ontrue()
; CHECK-NEXT:   call void @patatuccio()
; CHECK-NEXT:   ret void
; CHECK-NEXT: }

; CHECK-LABEL: define internal void @tinkywinky.1_ontrue() {
; CHECK-NEXT: newFuncRoot:
; CHECK-NEXT:   br label %ontrue
; CHECK: .exitStub:
; CHECK-NEXT:   ret void
; CHECK: ontrue:
; CHECK-NEXT:   call void @patatino()
; CHECK-NEXT:   br label %onfalse
; CHECK: onfalse:
; CHECK-NEXT:   br label %.exitStub
; CHECK-NEXT: }

declare void @patatino()
declare void @patatuccio()

define fastcc void @tinkywinky() {
  br i1 true, label %ontrue, label %onfalse
ontrue:
  call void @patatino()
  br label %onfalse
onfalse:
  call void @patatuccio()
  ret void
cantreachme:
  ret void
}
define void @dipsy() {
  call fastcc void @tinkywinky()
  ret void
}
