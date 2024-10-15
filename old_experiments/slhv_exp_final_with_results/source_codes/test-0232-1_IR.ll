; ModuleID = '/home/zhuyt/SESL/bin/b-70p3lpce.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.item = type { %struct.item*, %struct.item* }

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1
@.str.1 = private unnamed_addr constant [14 x i8] c"test-0232-1.c\00", align 1
@__PRETTY_FUNCTION__.reach_error = private unnamed_addr constant [19 x i8] c"void reach_error()\00", align 1

; Function Attrs: noinline nounwind uwtable
define internal void @reach_error() #0 !dbg !7 {
  call void @__assert_fail(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0), i8* getelementptr inbounds ([14 x i8], [14 x i8]* @.str.1, i64 0, i64 0), i32 3, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @__PRETTY_FUNCTION__.reach_error, i64 0, i64 0)) #5, !dbg !11, !verifier.code !14
  unreachable, !dbg !11, !verifier.code !14
}

; Function Attrs: noreturn nounwind
declare dso_local void @__assert_fail(i8*, i8*, i32, i8*) #1

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !15 {
  %1 = alloca %struct.item*, align 8, !verifier.code !14
  call void @llvm.dbg.declare(metadata %struct.item** %1, metadata !19, metadata !DIExpression()), !dbg !25, !verifier.code !14
  store %struct.item* null, %struct.item** %1, align 8, !dbg !25, !verifier.code !14
  br label %2, !dbg !26, !verifier.code !14

2:                                                ; preds = %3, %0
  call void @append(%struct.item** %1), !dbg !27, !verifier.code !14
  br label %3, !dbg !27, !verifier.code !14

3:                                                ; preds = %2
  %4 = call i32 @__VERIFIER_nondet_int(), !dbg !28, !verifier.code !29
  %5 = icmp ne i32 %4, 0, !dbg !27, !verifier.code !14
  br i1 %5, label %2, label %6, !dbg !27, !llvm.loop !30, !verifier.code !14

6:                                                ; preds = %3
  %7 = load %struct.item*, %struct.item** %1, align 8, !dbg !32, !verifier.code !14
  %8 = icmp ne %struct.item* %7, null, !dbg !32, !verifier.code !14
  br i1 %8, label %9, label %15, !dbg !34, !verifier.code !14

9:                                                ; preds = %6
  %10 = load %struct.item*, %struct.item** %1, align 8, !dbg !35, !verifier.code !14
  %11 = getelementptr inbounds %struct.item, %struct.item* %10, i32 0, i32 0, !dbg !37, !verifier.code !14
  %12 = load %struct.item*, %struct.item** %11, align 8, !dbg !37, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.item* %12, metadata !38, metadata !DIExpression()), !dbg !39, !verifier.code !14
  %13 = load %struct.item*, %struct.item** %1, align 8, !dbg !40, !verifier.code !14
  %14 = bitcast %struct.item* %13 to i8*, !dbg !40, !verifier.code !14
  call void @free(i8* %14) #6, !dbg !41, !verifier.code !14
  store %struct.item* %12, %struct.item** %1, align 8, !dbg !42, !verifier.code !14
  br label %15, !dbg !43, !verifier.code !14

15:                                               ; preds = %9, %6
  %16 = load %struct.item*, %struct.item** %1, align 8, !dbg !44, !verifier.code !14
  %17 = icmp ne %struct.item* %16, null, !dbg !45, !verifier.code !14
  br i1 %17, label %.lr.ph, label %26, !dbg !45, !verifier.code !14

.lr.ph:                                           ; preds = %15
  br label %18, !dbg !45, !verifier.code !14

18:                                               ; preds = %.lr.ph, %18
  %19 = load %struct.item*, %struct.item** %1, align 8, !dbg !46, !verifier.code !14
  %20 = getelementptr inbounds %struct.item, %struct.item* %19, i32 0, i32 0, !dbg !48, !verifier.code !14
  %21 = load %struct.item*, %struct.item** %20, align 8, !dbg !48, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.item* %21, metadata !49, metadata !DIExpression()), !dbg !50, !verifier.code !14
  %22 = load %struct.item*, %struct.item** %1, align 8, !dbg !51, !verifier.code !14
  %23 = bitcast %struct.item* %22 to i8*, !dbg !51, !verifier.code !14
  call void @free(i8* %23) #6, !dbg !52, !verifier.code !14
  store %struct.item* %21, %struct.item** %1, align 8, !dbg !53, !verifier.code !14
  %24 = load %struct.item*, %struct.item** %1, align 8, !dbg !44, !verifier.code !14
  %25 = icmp ne %struct.item* %24, null, !dbg !45, !verifier.code !14
  br i1 %25, label %18, label %._crit_edge, !dbg !45, !llvm.loop !54, !verifier.code !14

._crit_edge:                                      ; preds = %18
  br label %26, !dbg !45, !verifier.code !14

26:                                               ; preds = %._crit_edge, %15
  ret i32 0, !dbg !56, !verifier.code !14
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #2

; Function Attrs: noinline nounwind uwtable
define internal void @append(%struct.item** %0) #0 !dbg !57 {
  call void @llvm.dbg.value(metadata %struct.item** %0, metadata !61, metadata !DIExpression()), !dbg !62, !verifier.code !14
  %2 = call noalias i8* @malloc(i32 16) #6, !dbg !63, !verifier.code !14
  %3 = bitcast i8* %2 to %struct.item*, !dbg !63, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.item* %3, metadata !64, metadata !DIExpression()), !dbg !62, !verifier.code !14
  %4 = load %struct.item*, %struct.item** %0, align 8, !dbg !65, !verifier.code !14
  %5 = getelementptr inbounds %struct.item, %struct.item* %3, i32 0, i32 0, !dbg !66, !verifier.code !14
  store %struct.item* %4, %struct.item** %5, align 8, !dbg !67, !verifier.code !14
  %6 = getelementptr inbounds %struct.item, %struct.item* %3, i32 0, i32 0, !dbg !68, !verifier.code !14
  %7 = load %struct.item*, %struct.item** %6, align 8, !dbg !68, !verifier.code !14
  %8 = icmp ne %struct.item* %7, null, !dbg !69, !verifier.code !14
  br i1 %8, label %9, label %15, !dbg !69, !verifier.code !14

9:                                                ; preds = %1
  %10 = getelementptr inbounds %struct.item, %struct.item* %3, i32 0, i32 0, !dbg !70, !verifier.code !14
  %11 = load %struct.item*, %struct.item** %10, align 8, !dbg !70, !verifier.code !14
  %12 = getelementptr inbounds %struct.item, %struct.item* %11, i32 0, i32 1, !dbg !71, !verifier.code !14
  %13 = load %struct.item*, %struct.item** %12, align 8, !dbg !71, !verifier.code !14
  %14 = bitcast %struct.item* %13 to i8*, !dbg !72, !verifier.code !14
  br label %17, !dbg !69, !verifier.code !14

15:                                               ; preds = %1
  %16 = call noalias i8* @malloc(i32 16) #6, !dbg !73, !verifier.code !14
  br label %17, !dbg !69, !verifier.code !14

17:                                               ; preds = %15, %9
  %18 = phi i8* [ %14, %9 ], [ %16, %15 ], !dbg !69, !verifier.code !14
  %19 = bitcast i8* %18 to %struct.item*, !dbg !69, !verifier.code !14
  %20 = getelementptr inbounds %struct.item, %struct.item* %3, i32 0, i32 1, !dbg !74, !verifier.code !14
  store %struct.item* %19, %struct.item** %20, align 8, !dbg !75, !verifier.code !14
  store %struct.item* %3, %struct.item** %0, align 8, !dbg !76, !verifier.code !14
  ret void, !dbg !77, !verifier.code !14
}

declare dso_local i32 @__VERIFIER_nondet_int() #3

; Function Attrs: nounwind
declare dso_local void @free(i8*) #4

; Function Attrs: nounwind
declare dso_local noalias i8* @malloc(i32) #4

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.value(metadata, metadata, metadata) #2

define void @__SMACK_static_init() {
entry:
  ret void
}

attributes #0 = { noinline nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { noreturn nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { nounwind readnone speculatable willreturn }
attributes #3 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #5 = { noreturn nounwind }
attributes #6 = { nounwind }

!llvm.dbg.cu = !{!0}
!llvm.ident = !{!3}
!llvm.module.flags = !{!4, !5, !6}

!0 = distinct !DICompileUnit(language: DW_LANG_C99, file: !1, producer: "Ubuntu clang version 10.0.1-++20211003085942+ef32c611aa21-1~exp1~20211003090334.2", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !2, splitDebugInlining: false, nameTableKind: None)
!1 = !DIFile(filename: "/home/zhuyt/slhv_expr/source_codes/test-0232-1.i", directory: "/home/zhuyt/SESL/bin")
!2 = !{}
!3 = !{!"Ubuntu clang version 10.0.1-++20211003085942+ef32c611aa21-1~exp1~20211003090334.2"}
!4 = !{i32 7, !"Dwarf Version", i32 4}
!5 = !{i32 2, !"Debug Info Version", i32 3}
!6 = !{i32 1, !"wchar_size", i32 4}
!7 = distinct !DISubprogram(name: "reach_error", scope: !8, file: !8, line: 12, type: !9, scopeLine: 12, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!8 = !DIFile(filename: "slhv_expr/source_codes/test-0232-1.i", directory: "/home/zhuyt")
!9 = !DISubroutineType(types: !10)
!10 = !{null}
!11 = !DILocation(line: 12, column: 83, scope: !12)
!12 = distinct !DILexicalBlock(scope: !13, file: !8, line: 12, column: 73)
!13 = distinct !DILexicalBlock(scope: !7, file: !8, line: 12, column: 67)
!14 = !{i1 false}
!15 = distinct !DISubprogram(name: "main", scope: !8, file: !8, line: 537, type: !16, scopeLine: 538, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!16 = !DISubroutineType(types: !17)
!17 = !{!18}
!18 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!19 = !DILocalVariable(name: "list", scope: !15, file: !8, line: 539, type: !20)
!20 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !21, size: 64)
!21 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "item", file: !8, line: 524, size: 128, elements: !22)
!22 = !{!23, !24}
!23 = !DIDerivedType(tag: DW_TAG_member, name: "next", scope: !21, file: !8, line: 525, baseType: !20, size: 64)
!24 = !DIDerivedType(tag: DW_TAG_member, name: "data", scope: !21, file: !8, line: 526, baseType: !20, size: 64, offset: 64)
!25 = !DILocation(line: 539, column: 18, scope: !15)
!26 = !DILocation(line: 540, column: 5, scope: !15)
!27 = !DILocation(line: 541, column: 9, scope: !15)
!28 = !DILocation(line: 542, column: 12, scope: !15)
!29 = !{i1 true}
!30 = distinct !{!30, !26, !31}
!31 = !DILocation(line: 542, column: 35, scope: !15)
!32 = !DILocation(line: 543, column: 9, scope: !33)
!33 = distinct !DILexicalBlock(scope: !15, file: !8, line: 543, column: 9)
!34 = !DILocation(line: 543, column: 9, scope: !15)
!35 = !DILocation(line: 544, column: 29, scope: !36)
!36 = distinct !DILexicalBlock(scope: !33, file: !8, line: 543, column: 15)
!37 = !DILocation(line: 544, column: 35, scope: !36)
!38 = !DILocalVariable(name: "next", scope: !36, file: !8, line: 544, type: !20)
!39 = !DILocation(line: 0, scope: !36)
!40 = !DILocation(line: 545, column: 14, scope: !36)
!41 = !DILocation(line: 545, column: 9, scope: !36)
!42 = !DILocation(line: 546, column: 14, scope: !36)
!43 = !DILocation(line: 547, column: 5, scope: !36)
!44 = !DILocation(line: 548, column: 12, scope: !15)
!45 = !DILocation(line: 548, column: 5, scope: !15)
!46 = !DILocation(line: 549, column: 29, scope: !47)
!47 = distinct !DILexicalBlock(scope: !15, file: !8, line: 548, column: 18)
!48 = !DILocation(line: 549, column: 35, scope: !47)
!49 = !DILocalVariable(name: "next", scope: !47, file: !8, line: 549, type: !20)
!50 = !DILocation(line: 0, scope: !47)
!51 = !DILocation(line: 550, column: 14, scope: !47)
!52 = !DILocation(line: 550, column: 9, scope: !47)
!53 = !DILocation(line: 551, column: 14, scope: !47)
!54 = distinct !{!54, !45, !55}
!55 = !DILocation(line: 552, column: 5, scope: !15)
!56 = !DILocation(line: 553, column: 5, scope: !15)
!57 = distinct !DISubprogram(name: "append", scope: !8, file: !8, line: 528, type: !58, scopeLine: 529, flags: DIFlagPrototyped, spFlags: DISPFlagLocalToUnit | DISPFlagDefinition, unit: !0, retainedNodes: !2)
!58 = !DISubroutineType(types: !59)
!59 = !{null, !60}
!60 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !20, size: 64)
!61 = !DILocalVariable(name: "plist", arg: 1, scope: !57, file: !8, line: 528, type: !60)
!62 = !DILocation(line: 0, scope: !57)
!63 = !DILocation(line: 530, column: 25, scope: !57)
!64 = !DILocalVariable(name: "item", scope: !57, file: !8, line: 530, type: !20)
!65 = !DILocation(line: 531, column: 18, scope: !57)
!66 = !DILocation(line: 531, column: 11, scope: !57)
!67 = !DILocation(line: 531, column: 16, scope: !57)
!68 = !DILocation(line: 532, column: 25, scope: !57)
!69 = !DILocation(line: 532, column: 18, scope: !57)
!70 = !DILocation(line: 533, column: 17, scope: !57)
!71 = !DILocation(line: 533, column: 23, scope: !57)
!72 = !DILocation(line: 533, column: 11, scope: !57)
!73 = !DILocation(line: 534, column: 11, scope: !57)
!74 = !DILocation(line: 532, column: 11, scope: !57)
!75 = !DILocation(line: 532, column: 16, scope: !57)
!76 = !DILocation(line: 535, column: 12, scope: !57)
!77 = !DILocation(line: 536, column: 1, scope: !57)
