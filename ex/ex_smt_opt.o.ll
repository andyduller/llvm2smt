; ModuleID = 'ex_smt_opt.o'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i486-linux-gnu"

define i32 @fonction(i32 %x, i32 %y) nounwind {
entry:
  %tmp1 = icmp sgt i32 %x, 3                      ; <i1> [#uses=1]
  %tmp4 = icmp sgt i32 %y, 4                      ; <i1> [#uses=1]
  %or.cond = or i1 %tmp1, %tmp4                   ; <i1> [#uses=1]
  br i1 %or.cond, label %bb7, label %bb8

bb7:                                              ; preds = %entry
  tail call void (...)* @verif_stop() nounwind
  br label %bb8

bb8:                                              ; preds = %bb7, %entry
  %tmp11 = add i32 %y, %x                         ; <i32> [#uses=1]
  %tmp14 = icmp sgt i32 %tmp11, 6                 ; <i1> [#uses=1]
  br i1 %tmp14, label %bb17, label %return

bb17:                                             ; preds = %bb8
  tail call void (...)* @verif_warn() nounwind
  ret i32 undef

return:                                           ; preds = %bb8
  ret i32 undef
}

declare void @verif_stop(...)

declare void @verif_warn(...)
