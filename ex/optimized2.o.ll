; ModuleID = 'optimized2.o'
target datalayout = "e-p:32:32:32-i1:8:8-i8:8:8-i16:16:16-i32:32:32-i64:32:64-f32:32:32-f64:32:64-v64:64:64-v128:128:128-a0:0:64-f80:32:32-n8:16:32"
target triple = "i386-pc-linux-gnu"

define i32 @fonction(i32 %x, i32 %y) nounwind {
entry:
  br label %do.body

do.body:                                          ; preds = %entry
  %cmp = icmp sge i32 %x, 0                       ; <i1> [#uses=1]
  br i1 %cmp, label %land.lhs.true, label %if.then

land.lhs.true:                                    ; preds = %do.body
  %cmp2 = icmp sge i32 %y, 0                      ; <i1> [#uses=1]
  br i1 %cmp2, label %land.lhs.true3, label %if.then

land.lhs.true3:                                   ; preds = %land.lhs.true
  %cmp5 = icmp slt i32 %x, 4                      ; <i1> [#uses=1]
  br i1 %cmp5, label %land.lhs.true6, label %if.then

land.lhs.true6:                                   ; preds = %land.lhs.true3
  %cmp8 = icmp slt i32 %y, 5                      ; <i1> [#uses=1]
  br i1 %cmp8, label %if.end, label %if.then

if.then:                                          ; preds = %land.lhs.true6, %land.lhs.true3, %land.lhs.true, %do.body
  call void (...)* @verif_stop()
  br label %if.end

if.end:                                           ; preds = %if.then, %land.lhs.true6
  br label %do.end

do.end:                                           ; preds = %if.end
  %mul = mul i32 %x, %y                           ; <i32> [#uses=1]
  %add = add nsw i32 %mul, 2                      ; <i32> [#uses=2]
  br label %do.body11

do.body11:                                        ; preds = %do.end
  %cmp13 = icmp slt i32 %add, 100                 ; <i1> [#uses=1]
  br i1 %cmp13, label %if.end15, label %if.then14

if.then14:                                        ; preds = %do.body11
  call void (...)* @verif_warn()
  br label %if.end15

if.end15:                                         ; preds = %if.then14, %do.body11
  br label %do.end16

do.end16:                                         ; preds = %if.end15
  ret i32 %add
}

declare void @verif_stop(...)

declare void @verif_warn(...)
