; ModuleID = '/home/zhuyt/SESL/bin/b-xwhm2wou.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.cell = type { i32, %struct.cell* }

@pc1 = internal global i32 1, align 4, !dbg !0
@pc4 = internal global i32 1, align 4, !dbg !8
@S = internal global %struct.cell* null, align 8, !dbg !31
@garbage = internal global %struct.cell* null, align 8, !dbg !33
@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1
@.str.1 = private unnamed_addr constant [15 x i8] c"lockfree-3.0.c\00", align 1
@__PRETTY_FUNCTION__.reach_error = private unnamed_addr constant [19 x i8] c"void reach_error()\00", align 1
@push.x1 = internal global %struct.cell* null, align 8, !dbg !22
@push.t1 = internal global %struct.cell* null, align 8, !dbg !12
@pop.t4 = internal global %struct.cell* null, align 8, !dbg !24
@pop.x4 = internal global %struct.cell* null, align 8, !dbg !27
@pop.res4 = internal global i32 0, align 4, !dbg !29

; Function Attrs: noinline nounwind uwtable
define internal void @reach_error() #0 !dbg !39 {
  call void @__assert_fail(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0), i8* getelementptr inbounds ([15 x i8], [15 x i8]* @.str.1, i64 0, i64 0), i32 3, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @__PRETTY_FUNCTION__.reach_error, i64 0, i64 0)) #5, !dbg !40, !verifier.code !43
  unreachable, !dbg !40, !verifier.code !43
}

; Function Attrs: noreturn nounwind
declare dso_local void @__assert_fail(i8*, i8*, i32, i8*) #1

; Function Attrs: noinline nounwind uwtable
define internal void @push() #0 !dbg !14 {
  %1 = load i32, i32* @pc1, align 4, !dbg !44, !verifier.code !43
  %2 = add nsw i32 %1, 1, !dbg !44, !verifier.code !43
  store i32 %2, i32* @pc1, align 4, !dbg !44, !verifier.code !43
  br label %NodeBlock9, !verifier.code !43

NodeBlock9:                                       ; preds = %0
  %Pivot10 = icmp slt i32 %1, 4, !verifier.code !43
  br i1 %Pivot10, label %NodeBlock1, label %NodeBlock7, !verifier.code !43

NodeBlock7:                                       ; preds = %NodeBlock9
  %Pivot8 = icmp slt i32 %1, 5, !verifier.code !43
  br i1 %Pivot8, label %15, label %NodeBlock5, !verifier.code !43

NodeBlock5:                                       ; preds = %NodeBlock7
  %Pivot6 = icmp slt i32 %1, 6, !verifier.code !43
  br i1 %Pivot6, label %19, label %LeafBlock3, !verifier.code !43

LeafBlock3:                                       ; preds = %NodeBlock5
  %SwitchLeaf4 = icmp eq i32 %1, 6, !verifier.code !43
  br i1 %SwitchLeaf4, label %27, label %NewDefault, !verifier.code !43

NodeBlock1:                                       ; preds = %NodeBlock9
  %Pivot2 = icmp slt i32 %1, 2, !verifier.code !43
  br i1 %Pivot2, label %LeafBlock, label %NodeBlock, !verifier.code !43

NodeBlock:                                        ; preds = %NodeBlock1
  %Pivot = icmp slt i32 %1, 3, !verifier.code !43
  br i1 %Pivot, label %10, label %13, !verifier.code !43

LeafBlock:                                        ; preds = %NodeBlock1
  %SwitchLeaf = icmp eq i32 %1, 1, !verifier.code !43
  br i1 %SwitchLeaf, label %3, label %NewDefault, !verifier.code !43

3:                                                ; preds = %LeafBlock
  %4 = call noalias i8* @malloc(i32 16) #6, !dbg !45, !verifier.code !43
  %5 = bitcast i8* %4 to %struct.cell*, !dbg !45, !verifier.code !43
  store %struct.cell* %5, %struct.cell** @push.x1, align 8, !dbg !47, !verifier.code !43
  %6 = load %struct.cell*, %struct.cell** @push.x1, align 8, !dbg !48, !verifier.code !43
  %7 = getelementptr inbounds %struct.cell, %struct.cell* %6, i32 0, i32 0, !dbg !49, !verifier.code !43
  store i32 0, i32* %7, align 8, !dbg !50, !verifier.code !43
  %8 = load %struct.cell*, %struct.cell** @push.x1, align 8, !dbg !51, !verifier.code !43
  %9 = getelementptr inbounds %struct.cell, %struct.cell* %8, i32 0, i32 1, !dbg !52, !verifier.code !43
  store %struct.cell* null, %struct.cell** %9, align 8, !dbg !53, !verifier.code !43
  br label %28, !dbg !54, !verifier.code !43

10:                                               ; preds = %NodeBlock
  %11 = load %struct.cell*, %struct.cell** @push.x1, align 8, !dbg !55, !verifier.code !43
  %12 = getelementptr inbounds %struct.cell, %struct.cell* %11, i32 0, i32 0, !dbg !56, !verifier.code !43
  store i32 4, i32* %12, align 8, !dbg !57, !verifier.code !43
  br label %28, !dbg !58, !verifier.code !43

13:                                               ; preds = %NodeBlock
  %14 = load %struct.cell*, %struct.cell** @S, align 8, !dbg !59, !verifier.code !43
  store %struct.cell* %14, %struct.cell** @push.t1, align 8, !dbg !60, !verifier.code !43
  br label %28, !dbg !61, !verifier.code !43

15:                                               ; preds = %NodeBlock7
  %16 = load %struct.cell*, %struct.cell** @push.t1, align 8, !dbg !62, !verifier.code !43
  %17 = load %struct.cell*, %struct.cell** @push.x1, align 8, !dbg !63, !verifier.code !43
  %18 = getelementptr inbounds %struct.cell, %struct.cell* %17, i32 0, i32 1, !dbg !64, !verifier.code !43
  store %struct.cell* %16, %struct.cell** %18, align 8, !dbg !65, !verifier.code !43
  br label %28, !dbg !66, !verifier.code !43

19:                                               ; preds = %NodeBlock5
  %20 = load %struct.cell*, %struct.cell** @S, align 8, !dbg !67, !verifier.code !43
  %21 = load %struct.cell*, %struct.cell** @push.t1, align 8, !dbg !69, !verifier.code !43
  %22 = icmp eq %struct.cell* %20, %21, !dbg !70, !verifier.code !43
  br i1 %22, label %23, label %25, !dbg !71, !verifier.code !43

23:                                               ; preds = %19
  %24 = load %struct.cell*, %struct.cell** @push.x1, align 8, !dbg !72, !verifier.code !43
  store %struct.cell* %24, %struct.cell** @S, align 8, !dbg !73, !verifier.code !43
  br label %26, !dbg !74, !verifier.code !43

25:                                               ; preds = %19
  store i32 3, i32* @pc1, align 4, !dbg !75, !verifier.code !43
  br label %26, !verifier.code !43

26:                                               ; preds = %25, %23
  br label %28, !dbg !76, !verifier.code !43

27:                                               ; preds = %LeafBlock3
  store i32 1, i32* @pc1, align 4, !dbg !77, !verifier.code !43
  br label %28, !dbg !78, !verifier.code !43

NewDefault:                                       ; preds = %LeafBlock3, %LeafBlock
  br label %28, !verifier.code !43

28:                                               ; preds = %NewDefault, %3, %10, %13, %15, %26, %27
  ret void, !dbg !79, !verifier.code !43
}

; Function Attrs: nounwind
declare dso_local noalias i8* @malloc(i32) #2

; Function Attrs: noinline nounwind uwtable
define internal void @pop() #0 !dbg !26 {
  %1 = load i32, i32* @pc4, align 4, !dbg !80, !verifier.code !43
  %2 = add nsw i32 %1, 1, !dbg !80, !verifier.code !43
  store i32 %2, i32* @pc4, align 4, !dbg !80, !verifier.code !43
  br label %NodeBlock7, !verifier.code !43

NodeBlock7:                                       ; preds = %0
  %Pivot8 = icmp slt i32 %1, 3, !verifier.code !43
  br i1 %Pivot8, label %NodeBlock, label %NodeBlock5, !verifier.code !43

NodeBlock5:                                       ; preds = %NodeBlock7
  %Pivot6 = icmp slt i32 %1, 4, !verifier.code !43
  br i1 %Pivot6, label %10, label %NodeBlock3, !verifier.code !43

NodeBlock3:                                       ; preds = %NodeBlock5
  %Pivot4 = icmp slt i32 %1, 5, !verifier.code !43
  br i1 %Pivot4, label %14, label %LeafBlock1, !verifier.code !43

LeafBlock1:                                       ; preds = %NodeBlock3
  %SwitchLeaf2 = icmp eq i32 %1, 5, !verifier.code !43
  br i1 %SwitchLeaf2, label %22, label %NewDefault, !verifier.code !43

NodeBlock:                                        ; preds = %NodeBlock7
  %Pivot = icmp slt i32 %1, 2, !verifier.code !43
  br i1 %Pivot, label %LeafBlock, label %5, !verifier.code !43

LeafBlock:                                        ; preds = %NodeBlock
  %SwitchLeaf = icmp eq i32 %1, 1, !verifier.code !43
  br i1 %SwitchLeaf, label %3, label %NewDefault, !verifier.code !43

3:                                                ; preds = %LeafBlock
  %4 = load %struct.cell*, %struct.cell** @S, align 8, !dbg !81, !verifier.code !43
  store %struct.cell* %4, %struct.cell** @pop.t4, align 8, !dbg !83, !verifier.code !43
  br label %30, !dbg !84, !verifier.code !43

5:                                                ; preds = %NodeBlock
  %6 = load %struct.cell*, %struct.cell** @pop.t4, align 8, !dbg !85, !verifier.code !43
  %7 = icmp eq %struct.cell* %6, null, !dbg !87, !verifier.code !43
  br i1 %7, label %8, label %9, !dbg !88, !verifier.code !43

8:                                                ; preds = %5
  store i32 1, i32* @pc4, align 4, !dbg !89, !verifier.code !43
  br label %9, !dbg !90, !verifier.code !43

9:                                                ; preds = %8, %5
  br label %30, !dbg !91, !verifier.code !43

10:                                               ; preds = %NodeBlock5
  %11 = load %struct.cell*, %struct.cell** @pop.t4, align 8, !dbg !92, !verifier.code !43
  %12 = getelementptr inbounds %struct.cell, %struct.cell* %11, i32 0, i32 1, !dbg !93, !verifier.code !43
  %13 = load %struct.cell*, %struct.cell** %12, align 8, !dbg !93, !verifier.code !43
  store %struct.cell* %13, %struct.cell** @pop.x4, align 8, !dbg !94, !verifier.code !43
  br label %30, !dbg !95, !verifier.code !43

14:                                               ; preds = %NodeBlock3
  %15 = load %struct.cell*, %struct.cell** @S, align 8, !dbg !96, !verifier.code !43
  %16 = load %struct.cell*, %struct.cell** @pop.t4, align 8, !dbg !98, !verifier.code !43
  %17 = icmp eq %struct.cell* %15, %16, !dbg !99, !verifier.code !43
  br i1 %17, label %18, label %20, !dbg !100, !verifier.code !43

18:                                               ; preds = %14
  %19 = load %struct.cell*, %struct.cell** @pop.x4, align 8, !dbg !101, !verifier.code !43
  store %struct.cell* %19, %struct.cell** @S, align 8, !dbg !102, !verifier.code !43
  br label %21, !dbg !103, !verifier.code !43

20:                                               ; preds = %14
  store i32 1, i32* @pc4, align 4, !dbg !104, !verifier.code !43
  br label %21, !verifier.code !43

21:                                               ; preds = %20, %18
  br label %30, !dbg !105, !verifier.code !43

22:                                               ; preds = %LeafBlock1
  %23 = load %struct.cell*, %struct.cell** @pop.t4, align 8, !dbg !106, !verifier.code !43
  %24 = getelementptr inbounds %struct.cell, %struct.cell* %23, i32 0, i32 0, !dbg !107, !verifier.code !43
  %25 = load i32, i32* %24, align 8, !dbg !107, !verifier.code !43
  store i32 %25, i32* @pop.res4, align 4, !dbg !108, !verifier.code !43
  %26 = load %struct.cell*, %struct.cell** @garbage, align 8, !dbg !109, !verifier.code !43
  %27 = load %struct.cell*, %struct.cell** @pop.t4, align 8, !dbg !110, !verifier.code !43
  %28 = getelementptr inbounds %struct.cell, %struct.cell* %27, i32 0, i32 1, !dbg !111, !verifier.code !43
  store %struct.cell* %26, %struct.cell** %28, align 8, !dbg !112, !verifier.code !43
  %29 = load %struct.cell*, %struct.cell** @pop.t4, align 8, !dbg !113, !verifier.code !43
  store %struct.cell* %29, %struct.cell** @garbage, align 8, !dbg !114, !verifier.code !43
  store i32 1, i32* @pc4, align 4, !dbg !115, !verifier.code !43
  br label %30, !dbg !116, !verifier.code !43

NewDefault:                                       ; preds = %LeafBlock1, %LeafBlock
  br label %30, !verifier.code !43

30:                                               ; preds = %NewDefault, %3, %9, %10, %21, %22
  ret void, !dbg !117, !verifier.code !43
}

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !118 {
  br label %1, !dbg !121, !verifier.code !43

1:                                                ; preds = %20, %0
  %2 = load %struct.cell*, %struct.cell** @S, align 8, !dbg !122, !verifier.code !43
  %3 = icmp ne %struct.cell* %2, null, !dbg !122, !verifier.code !43
  br i1 %3, label %13, label %4, !dbg !123, !verifier.code !43

4:                                                ; preds = %1
  %5 = load i32, i32* @pc1, align 4, !dbg !124, !verifier.code !43
  %6 = icmp ne i32 1, %5, !dbg !125, !verifier.code !43
  br i1 %6, label %13, label %7, !dbg !126, !verifier.code !43

7:                                                ; preds = %4
  %8 = load i32, i32* @pc4, align 4, !dbg !127, !verifier.code !43
  %9 = icmp ne i32 1, %8, !dbg !128, !verifier.code !43
  br i1 %9, label %13, label %10, !dbg !129, !verifier.code !43

10:                                               ; preds = %7
  %11 = call i32 @__VERIFIER_nondet_int(), !dbg !130, !verifier.code !131
  %12 = icmp ne i32 %11, 0, !dbg !129, !verifier.code !43
  br label %13, !dbg !129, !verifier.code !43

13:                                               ; preds = %10, %7, %4, %1
  %14 = phi i1 [ true, %7 ], [ true, %4 ], [ true, %1 ], [ %12, %10 ], !verifier.code !43
  br i1 %14, label %15, label %21, !dbg !121, !verifier.code !43

15:                                               ; preds = %13
  %16 = call i32 @__VERIFIER_nondet_int(), !dbg !132, !verifier.code !131
  %17 = icmp ne i32 %16, 0, !dbg !132, !verifier.code !43
  br i1 %17, label %18, label %19, !dbg !135, !verifier.code !43

18:                                               ; preds = %15
  call void @push(), !dbg !136, !verifier.code !43
  br label %20, !dbg !136, !verifier.code !43

19:                                               ; preds = %15
  call void @pop(), !dbg !137, !verifier.code !43
  br label %20, !verifier.code !43

20:                                               ; preds = %19, %18
  br label %1, !dbg !121, !llvm.loop !138, !verifier.code !43

21:                                               ; preds = %13
  %22 = load %struct.cell*, %struct.cell** @garbage, align 8, !dbg !140, !verifier.code !43
  %23 = icmp ne %struct.cell* %22, null, !dbg !141, !verifier.code !43
  br i1 %23, label %.lr.ph, label %32, !dbg !141, !verifier.code !43

.lr.ph:                                           ; preds = %21
  br label %24, !dbg !141, !verifier.code !43

24:                                               ; preds = %.lr.ph, %24
  %25 = load %struct.cell*, %struct.cell** @garbage, align 8, !dbg !142, !verifier.code !43
  %26 = getelementptr inbounds %struct.cell, %struct.cell* %25, i32 0, i32 1, !dbg !144, !verifier.code !43
  %27 = load %struct.cell*, %struct.cell** %26, align 8, !dbg !144, !verifier.code !43
  call void @llvm.dbg.value(metadata %struct.cell* %27, metadata !145, metadata !DIExpression()), !dbg !146, !verifier.code !43
  %28 = load %struct.cell*, %struct.cell** @garbage, align 8, !dbg !147, !verifier.code !43
  %29 = bitcast %struct.cell* %28 to i8*, !dbg !147, !verifier.code !43
  call void @free(i8* %29) #6, !dbg !148, !verifier.code !43
  store %struct.cell* %27, %struct.cell** @garbage, align 8, !dbg !149, !verifier.code !43
  %30 = load %struct.cell*, %struct.cell** @garbage, align 8, !dbg !140, !verifier.code !43
  %31 = icmp ne %struct.cell* %30, null, !dbg !141, !verifier.code !43
  br i1 %31, label %24, label %._crit_edge, !dbg !141, !llvm.loop !150, !verifier.code !43

._crit_edge:                                      ; preds = %24
  br label %32, !dbg !141, !verifier.code !43

32:                                               ; preds = %._crit_edge, %21
  %33 = load %struct.cell*, %struct.cell** @garbage, align 8, !dbg !152, !verifier.code !43
  %34 = icmp ne %struct.cell* %33, null, !dbg !153, !verifier.code !43
  %35 = xor i1 %34, true, !dbg !153, !verifier.code !43
  %36 = xor i1 %35, true, !dbg !154, !verifier.code !43
  %37 = zext i1 %36 to i32, !dbg !154, !verifier.code !43
  ret i32 %37, !dbg !155, !verifier.code !43
}

declare dso_local i32 @__VERIFIER_nondet_int() #3

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #4

; Function Attrs: nounwind
declare dso_local void @free(i8*) #2

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.value(metadata, metadata, metadata) #4

define void @__SMACK_static_init() {
entry:
  store i32 1, i32* @pc1
  store i32 1, i32* @pc4
  store %struct.cell* null, %struct.cell** @S
  store %struct.cell* null, %struct.cell** @garbage
  store %struct.cell* null, %struct.cell** @push.x1
  store %struct.cell* null, %struct.cell** @push.t1
  store %struct.cell* null, %struct.cell** @pop.t4
  store %struct.cell* null, %struct.cell** @pop.x4
  ret void
}

attributes #0 = { noinline nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind readnone speculatable willreturn }
attributes #5 = { noreturn nounwind }
attributes #6 = { nounwind }

!llvm.dbg.cu = !{!2}
!llvm.ident = !{!35}
!llvm.module.flags = !{!36, !37, !38}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "pc1", scope: !2, file: !10, line: 529, type: !11, isLocal: false, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C99, file: !3, producer: "Ubuntu clang version 10.0.1-++20211003085942+ef32c611aa21-1~exp1~20211003090334.2", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !4, retainedTypes: !5, globals: !7, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "/home/zhuyt/slhv_expr/source_codes/lockfree-3.0.i", directory: "/home/zhuyt/SESL/bin")
!4 = !{}
!5 = !{!6}
!6 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!7 = !{!0, !8, !12, !22, !24, !27, !29, !31, !33}
!8 = !DIGlobalVariableExpression(var: !9, expr: !DIExpression())
!9 = distinct !DIGlobalVariable(name: "pc4", scope: !2, file: !10, line: 530, type: !11, isLocal: false, isDefinition: true)
!10 = !DIFile(filename: "slhv_expr/source_codes/lockfree-3.0.i", directory: "/home/zhuyt")
!11 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!12 = !DIGlobalVariableExpression(var: !13, expr: !DIExpression())
!13 = distinct !DIGlobalVariable(name: "t1", scope: !14, file: !10, line: 533, type: !17, isLocal: true, isDefinition: true)
!14 = distinct !DISubprogram(name: "push", scope: !10, file: !10, line: 531, type: !15, scopeLine: 532, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !4)
!15 = !DISubroutineType(types: !16)
!16 = !{null}
!17 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !18, size: 64)
!18 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "cell", file: !10, line: 524, size: 128, elements: !19)
!19 = !{!20, !21}
!20 = !DIDerivedType(tag: DW_TAG_member, name: "data", scope: !18, file: !10, line: 525, baseType: !11, size: 32)
!21 = !DIDerivedType(tag: DW_TAG_member, name: "next", scope: !18, file: !10, line: 526, baseType: !17, size: 64, offset: 64)
!22 = !DIGlobalVariableExpression(var: !23, expr: !DIExpression())
!23 = distinct !DIGlobalVariable(name: "x1", scope: !14, file: !10, line: 534, type: !17, isLocal: true, isDefinition: true)
!24 = !DIGlobalVariableExpression(var: !25, expr: !DIExpression())
!25 = distinct !DIGlobalVariable(name: "t4", scope: !26, file: !10, line: 564, type: !17, isLocal: true, isDefinition: true)
!26 = distinct !DISubprogram(name: "pop", scope: !10, file: !10, line: 562, type: !15, scopeLine: 563, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !4)
!27 = !DIGlobalVariableExpression(var: !28, expr: !DIExpression())
!28 = distinct !DIGlobalVariable(name: "x4", scope: !26, file: !10, line: 565, type: !17, isLocal: true, isDefinition: true)
!29 = !DIGlobalVariableExpression(var: !30, expr: !DIExpression())
!30 = distinct !DIGlobalVariable(name: "res4", scope: !26, file: !10, line: 566, type: !11, isLocal: true, isDefinition: true)
!31 = !DIGlobalVariableExpression(var: !32, expr: !DIExpression())
!32 = distinct !DIGlobalVariable(name: "S", scope: !2, file: !10, line: 528, type: !17, isLocal: false, isDefinition: true)
!33 = !DIGlobalVariableExpression(var: !34, expr: !DIExpression())
!34 = distinct !DIGlobalVariable(name: "garbage", scope: !2, file: !10, line: 561, type: !17, isLocal: false, isDefinition: true)
!35 = !{!"Ubuntu clang version 10.0.1-++20211003085942+ef32c611aa21-1~exp1~20211003090334.2"}
!36 = !{i32 7, !"Dwarf Version", i32 4}
!37 = !{i32 2, !"Debug Info Version", i32 3}
!38 = !{i32 1, !"wchar_size", i32 4}
!39 = distinct !DISubprogram(name: "reach_error", scope: !10, file: !10, line: 12, type: !15, scopeLine: 12, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !4)
!40 = !DILocation(line: 12, column: 83, scope: !41)
!41 = distinct !DILexicalBlock(scope: !42, file: !10, line: 12, column: 73)
!42 = distinct !DILexicalBlock(scope: !39, file: !10, line: 12, column: 67)
!43 = !{i1 false}
!44 = !DILocation(line: 535, column: 16, scope: !14)
!45 = !DILocation(line: 537, column: 18, scope: !46)
!46 = distinct !DILexicalBlock(scope: !14, file: !10, line: 535, column: 20)
!47 = !DILocation(line: 537, column: 16, scope: !46)
!48 = !DILocation(line: 538, column: 13, scope: !46)
!49 = !DILocation(line: 538, column: 17, scope: !46)
!50 = !DILocation(line: 538, column: 22, scope: !46)
!51 = !DILocation(line: 539, column: 13, scope: !46)
!52 = !DILocation(line: 539, column: 17, scope: !46)
!53 = !DILocation(line: 539, column: 22, scope: !46)
!54 = !DILocation(line: 540, column: 13, scope: !46)
!55 = !DILocation(line: 542, column: 13, scope: !46)
!56 = !DILocation(line: 542, column: 17, scope: !46)
!57 = !DILocation(line: 542, column: 22, scope: !46)
!58 = !DILocation(line: 543, column: 13, scope: !46)
!59 = !DILocation(line: 545, column: 18, scope: !46)
!60 = !DILocation(line: 545, column: 16, scope: !46)
!61 = !DILocation(line: 546, column: 13, scope: !46)
!62 = !DILocation(line: 548, column: 24, scope: !46)
!63 = !DILocation(line: 548, column: 13, scope: !46)
!64 = !DILocation(line: 548, column: 17, scope: !46)
!65 = !DILocation(line: 548, column: 22, scope: !46)
!66 = !DILocation(line: 549, column: 13, scope: !46)
!67 = !DILocation(line: 551, column: 17, scope: !68)
!68 = distinct !DILexicalBlock(scope: !46, file: !10, line: 551, column: 17)
!69 = !DILocation(line: 551, column: 22, scope: !68)
!70 = !DILocation(line: 551, column: 19, scope: !68)
!71 = !DILocation(line: 551, column: 17, scope: !46)
!72 = !DILocation(line: 552, column: 21, scope: !68)
!73 = !DILocation(line: 552, column: 19, scope: !68)
!74 = !DILocation(line: 552, column: 17, scope: !68)
!75 = !DILocation(line: 554, column: 21, scope: !68)
!76 = !DILocation(line: 555, column: 13, scope: !46)
!77 = !DILocation(line: 557, column: 17, scope: !46)
!78 = !DILocation(line: 558, column: 13, scope: !46)
!79 = !DILocation(line: 560, column: 1, scope: !14)
!80 = !DILocation(line: 567, column: 16, scope: !26)
!81 = !DILocation(line: 569, column: 18, scope: !82)
!82 = distinct !DILexicalBlock(scope: !26, file: !10, line: 567, column: 20)
!83 = !DILocation(line: 569, column: 16, scope: !82)
!84 = !DILocation(line: 570, column: 13, scope: !82)
!85 = !DILocation(line: 572, column: 16, scope: !86)
!86 = distinct !DILexicalBlock(scope: !82, file: !10, line: 572, column: 16)
!87 = !DILocation(line: 572, column: 19, scope: !86)
!88 = !DILocation(line: 572, column: 16, scope: !82)
!89 = !DILocation(line: 573, column: 21, scope: !86)
!90 = !DILocation(line: 573, column: 17, scope: !86)
!91 = !DILocation(line: 574, column: 13, scope: !82)
!92 = !DILocation(line: 576, column: 18, scope: !82)
!93 = !DILocation(line: 576, column: 22, scope: !82)
!94 = !DILocation(line: 576, column: 16, scope: !82)
!95 = !DILocation(line: 577, column: 13, scope: !82)
!96 = !DILocation(line: 579, column: 17, scope: !97)
!97 = distinct !DILexicalBlock(scope: !82, file: !10, line: 579, column: 17)
!98 = !DILocation(line: 579, column: 22, scope: !97)
!99 = !DILocation(line: 579, column: 19, scope: !97)
!100 = !DILocation(line: 579, column: 17, scope: !82)
!101 = !DILocation(line: 580, column: 21, scope: !97)
!102 = !DILocation(line: 580, column: 19, scope: !97)
!103 = !DILocation(line: 580, column: 17, scope: !97)
!104 = !DILocation(line: 582, column: 21, scope: !97)
!105 = !DILocation(line: 583, column: 13, scope: !82)
!106 = !DILocation(line: 585, column: 20, scope: !82)
!107 = !DILocation(line: 585, column: 24, scope: !82)
!108 = !DILocation(line: 585, column: 18, scope: !82)
!109 = !DILocation(line: 586, column: 24, scope: !82)
!110 = !DILocation(line: 586, column: 13, scope: !82)
!111 = !DILocation(line: 586, column: 17, scope: !82)
!112 = !DILocation(line: 586, column: 22, scope: !82)
!113 = !DILocation(line: 587, column: 23, scope: !82)
!114 = !DILocation(line: 587, column: 21, scope: !82)
!115 = !DILocation(line: 588, column: 17, scope: !82)
!116 = !DILocation(line: 589, column: 13, scope: !82)
!117 = !DILocation(line: 591, column: 1, scope: !26)
!118 = distinct !DISubprogram(name: "main", scope: !10, file: !10, line: 592, type: !119, scopeLine: 593, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !4)
!119 = !DISubroutineType(types: !120)
!120 = !{!11}
!121 = !DILocation(line: 594, column: 5, scope: !118)
!122 = !DILocation(line: 594, column: 12, scope: !118)
!123 = !DILocation(line: 594, column: 14, scope: !118)
!124 = !DILocation(line: 594, column: 22, scope: !118)
!125 = !DILocation(line: 594, column: 19, scope: !118)
!126 = !DILocation(line: 594, column: 26, scope: !118)
!127 = !DILocation(line: 594, column: 34, scope: !118)
!128 = !DILocation(line: 594, column: 31, scope: !118)
!129 = !DILocation(line: 594, column: 38, scope: !118)
!130 = !DILocation(line: 594, column: 41, scope: !118)
!131 = !{i1 true}
!132 = !DILocation(line: 595, column: 13, scope: !133)
!133 = distinct !DILexicalBlock(scope: !134, file: !10, line: 595, column: 13)
!134 = distinct !DILexicalBlock(scope: !118, file: !10, line: 594, column: 66)
!135 = !DILocation(line: 595, column: 13, scope: !134)
!136 = !DILocation(line: 596, column: 13, scope: !133)
!137 = !DILocation(line: 598, column: 13, scope: !133)
!138 = distinct !{!138, !121, !139}
!139 = !DILocation(line: 599, column: 5, scope: !118)
!140 = !DILocation(line: 600, column: 12, scope: !118)
!141 = !DILocation(line: 600, column: 5, scope: !118)
!142 = !DILocation(line: 601, column: 29, scope: !143)
!143 = distinct !DILexicalBlock(scope: !118, file: !10, line: 600, column: 21)
!144 = !DILocation(line: 601, column: 38, scope: !143)
!145 = !DILocalVariable(name: "next", scope: !143, file: !10, line: 601, type: !17)
!146 = !DILocation(line: 0, scope: !143)
!147 = !DILocation(line: 602, column: 14, scope: !143)
!148 = !DILocation(line: 602, column: 9, scope: !143)
!149 = !DILocation(line: 603, column: 17, scope: !143)
!150 = distinct !{!150, !141, !151}
!151 = !DILocation(line: 604, column: 5, scope: !118)
!152 = !DILocation(line: 605, column: 14, scope: !118)
!153 = !DILocation(line: 605, column: 13, scope: !118)
!154 = !DILocation(line: 605, column: 12, scope: !118)
!155 = !DILocation(line: 605, column: 5, scope: !118)
