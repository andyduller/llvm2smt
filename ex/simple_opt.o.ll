; ModuleID = 'simple_opt.o'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32"
target triple = "i386-linux-gnu"

define i32 @main(i32 %argc, i8** %argv) nounwind {
entry:
  %"alloca point" = bitcast i32 0 to i32          ; <i32> [#uses=0]
  %0 = add nsw i32 2, 6                           ; <i32> [#uses=2]
  %1 = sub i32 8, 2                               ; <i32> [#uses=2]
  %2 = add nsw i32 %0, 8                          ; <i32> [#uses=1]
  %3 = add nsw i32 %1, 8                          ; <i32> [#uses=1]
  %4 = add nsw i32 %3, 42                         ; <i32> [#uses=1]
  %5 = add nsw i32 %4, 6                          ; <i32> [#uses=1]
  %6 = add nsw i32 %5, 8                          ; <i32> [#uses=1]
  %7 = add nsw i32 %6, %0                         ; <i32> [#uses=1]
  %8 = add nsw i32 %7, %1                         ; <i32> [#uses=1]
  %9 = add nsw i32 %8, %2                         ; <i32> [#uses=1]
  %10 = add nsw i32 %9, undef                     ; <i32> [#uses=1]
  br label %return

return:                                           ; preds = %entry
  ret i32 %10
}
