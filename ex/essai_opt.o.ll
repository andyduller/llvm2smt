; ModuleID = 'essai_opt.o'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-linux-gnu"

define i32 @main(i32 %argc, i8** %argv) nounwind {
entry:
  %"alloca point" = bitcast i32 0 to i32          ; <i32> [#uses=0]
  %0 = add nsw i32 2, 5                           ; <i32> [#uses=1]
  %1 = icmp sgt i32 %0, 0                         ; <i1> [#uses=1]
  br i1 %1, label %bb, label %bb1

bb:                                               ; preds = %entry
  br label %bb2

bb1:                                              ; preds = %entry
  br label %bb2

bb2:                                              ; preds = %bb1, %bb
  %x.0 = phi i32 [ 8, %bb ], [ 12, %bb1 ]         ; <i32> [#uses=1]
  %2 = add nsw i32 %x.0, 1                        ; <i32> [#uses=1]
  br label %return

return:                                           ; preds = %bb2
  ret i32 %2
}
