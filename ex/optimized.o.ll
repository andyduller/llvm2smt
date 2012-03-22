; ModuleID = 'optimized.o'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32"
target triple = "i386-pc-linux-gnu"

define i32 @fonction(i32 %x, i32 %y) nounwind {
entry:
  %cmp = icmp sgt i32 %x, -1                      ; <i1> [#uses=1]
  %cmp2 = icmp sgt i32 %y, -1                     ; <i1> [#uses=1]
  %or.cond = and i1 %cmp, %cmp2                   ; <i1> [#uses=1]
  %cmp5 = icmp slt i32 %x, 4                      ; <i1> [#uses=1]
  %or.cond1 = and i1 %or.cond, %cmp5              ; <i1> [#uses=1]
  %cmp8 = icmp slt i32 %y, 5                      ; <i1> [#uses=1]
  %or.cond2 = and i1 %or.cond1, %cmp8             ; <i1> [#uses=1]
  br i1 %or.cond2, label %do.end, label %if.then

if.then:                                          ; preds = %entry
  tail call void (...)* @verif_stop() nounwind
  br label %do.end

do.end:                                           ; preds = %if.then, %entry
  %mul = mul i32 %y, %x                           ; <i32> [#uses=1]
  %add = add nsw i32 %mul, 2                      ; <i32> [#uses=3]
  %cmp13 = icmp slt i32 %add, 100                 ; <i1> [#uses=1]
  br i1 %cmp13, label %do.end16, label %if.then14

if.then14:                                        ; preds = %do.end
  tail call void (...)* @verif_warn() nounwind
  ret i32 %add

do.end16:                                         ; preds = %do.end
  ret i32 %add
}

declare void @verif_stop(...)

declare void @verif_warn(...)
