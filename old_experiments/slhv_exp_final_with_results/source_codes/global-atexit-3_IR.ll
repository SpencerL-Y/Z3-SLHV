; ModuleID = '/home/zhuyt/SESL/bin/b-by3elk0j.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

@g = internal global i32** null, align 8, !dbg !0

; Function Attrs: noinline nounwind uwtable
define internal void @free_g1() #0 !dbg !16 {
  %1 = load i32**, i32*** @g, align 8, !dbg !19, !verifier.code !20
  %2 = bitcast i32** %1 to i8*, !dbg !19, !verifier.code !20
  call void @free(i8* %2) #4, !dbg !21, !verifier.code !20
  store i32** null, i32*** @g, align 8, !dbg !22, !verifier.code !20
  ret void, !dbg !23, !verifier.code !20
}

; Function Attrs: nounwind
declare dso_local void @free(i8*) #1

; Function Attrs: noinline nounwind uwtable
define internal void @free_g2() #0 !dbg !24 {
  %1 = load i32**, i32*** @g, align 8, !dbg !25, !verifier.code !20
  %2 = icmp ne i32** %1, null, !dbg !27, !verifier.code !20
  br i1 %2, label %3, label %7, !dbg !28, !verifier.code !20

3:                                                ; preds = %0
  %4 = load i32**, i32*** @g, align 8, !dbg !29, !verifier.code !20
  %5 = load i32*, i32** %4, align 8, !dbg !30, !verifier.code !20
  %6 = bitcast i32* %5 to i8*, !dbg !30, !verifier.code !20
  call void @free(i8* %6) #4, !dbg !31, !verifier.code !20
  br label %7, !dbg !31, !verifier.code !20

7:                                                ; preds = %3, %0
  ret void, !dbg !32, !verifier.code !20
}

; Function Attrs: noinline nounwind uwtable
define internal void @h() #0 !dbg !33 {
  %1 = call zeroext i1 (...) @__VERIFIER_nondet_bool(), !dbg !34, !verifier.code !36
  br i1 %1, label %2, label %3, !dbg !37, !verifier.code !20

2:                                                ; preds = %0
  call void @exit(i32 1) #5, !dbg !38, !verifier.code !20
  unreachable, !dbg !38, !verifier.code !20

3:                                                ; preds = %0
  ret void, !dbg !39, !verifier.code !20
}

declare dso_local zeroext i1 @__VERIFIER_nondet_bool(...) #2

; Function Attrs: noreturn nounwind
declare dso_local void @exit(i32) #3

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !40 {
  %1 = call noalias i8* @malloc(i32 8) #4, !dbg !43, !verifier.code !20
  %2 = bitcast i8* %1 to i32**, !dbg !44, !verifier.code !20
  store i32** %2, i32*** @g, align 8, !dbg !45, !verifier.code !20
  %3 = call zeroext i1 (...) @__VERIFIER_nondet_bool(), !dbg !46, !verifier.code !36
  br i1 %3, label %4, label %5, !dbg !48, !verifier.code !20

4:                                                ; preds = %0
  call void @exit(i32 1) #5, !dbg !49, !verifier.code !20
  unreachable, !dbg !49, !verifier.code !20

5:                                                ; preds = %0
  %6 = call noalias i8* @malloc(i32 4) #4, !dbg !50, !verifier.code !20
  %7 = bitcast i8* %6 to i32*, !dbg !51, !verifier.code !20
  %8 = load i32**, i32*** @g, align 8, !dbg !52, !verifier.code !20
  store i32* %7, i32** %8, align 8, !dbg !53, !verifier.code !20
  call void @h(), !dbg !54, !verifier.code !20
  %9 = load i32**, i32*** @g, align 8, !dbg !55, !verifier.code !20
  %10 = load i32*, i32** %9, align 8, !dbg !56, !verifier.code !20
  %11 = bitcast i32* %10 to i8*, !dbg !56, !verifier.code !20
  call void @free(i8* %11) #4, !dbg !57, !verifier.code !20
  %12 = load i32**, i32*** @g, align 8, !dbg !58, !verifier.code !20
  %13 = bitcast i32** %12 to i8*, !dbg !58, !verifier.code !20
  call void @free(i8* %13) #4, !dbg !59, !verifier.code !20
  store i32** null, i32*** @g, align 8, !dbg !60, !verifier.code !20
  call void @free_g2(), !dbg !61, !verifier.code !20
  ret i32 0, !dbg !62, !verifier.code !20
}

; Function Attrs: nounwind
declare dso_local noalias i8* @malloc(i32) #1

define void @__SMACK_static_init() {
entry:
  store i32** null, i32*** @g
  ret void
}

attributes #0 = { noinline nounwind uwtable "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "min-legal-vector-width"="0" "no-infs-fp-math"="false" "no-jump-tables"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #1 = { nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #2 = { "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #3 = { noreturn nounwind "correctly-rounded-divide-sqrt-fp-math"="false" "disable-tail-calls"="false" "frame-pointer"="all" "less-precise-fpmad"="false" "no-infs-fp-math"="false" "no-nans-fp-math"="false" "no-signed-zeros-fp-math"="false" "no-trapping-math"="false" "stack-protector-buffer-size"="8" "target-cpu"="x86-64" "target-features"="+cx8,+fxsr,+mmx,+sse,+sse2,+x87" "unsafe-fp-math"="false" "use-soft-float"="false" }
attributes #4 = { nounwind }
attributes #5 = { noreturn nounwind }

!llvm.dbg.cu = !{!2}
!llvm.ident = !{!12}
!llvm.module.flags = !{!13, !14, !15}

!0 = !DIGlobalVariableExpression(var: !1, expr: !DIExpression())
!1 = distinct !DIGlobalVariable(name: "g", scope: !2, file: !11, line: 556, type: !7, isLocal: false, isDefinition: true)
!2 = distinct !DICompileUnit(language: DW_LANG_C99, file: !3, producer: "Ubuntu clang version 10.0.1-++20211003085942+ef32c611aa21-1~exp1~20211003090334.2", isOptimized: false, runtimeVersion: 0, emissionKind: FullDebug, enums: !4, retainedTypes: !5, globals: !10, splitDebugInlining: false, nameTableKind: None)
!3 = !DIFile(filename: "/home/zhuyt/slhv_expr/source_codes/global-atexit-3.i", directory: "/home/zhuyt/SESL/bin")
!4 = !{}
!5 = !{!6, !7, !8}
!6 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: null, size: 64)
!7 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !8, size: 64)
!8 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !9, size: 64)
!9 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!10 = !{!0}
!11 = !DIFile(filename: "slhv_expr/source_codes/global-atexit-3.i", directory: "/home/zhuyt")
!12 = !{!"Ubuntu clang version 10.0.1-++20211003085942+ef32c611aa21-1~exp1~20211003090334.2"}
!13 = !{i32 7, !"Dwarf Version", i32 4}
!14 = !{i32 2, !"Debug Info Version", i32 3}
!15 = !{i32 1, !"wchar_size", i32 4}
!16 = distinct !DISubprogram(name: "free_g1", scope: !11, file: !11, line: 557, type: !17, scopeLine: 557, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !4)
!17 = !DISubroutineType(types: !18)
!18 = !{null}
!19 = !DILocation(line: 558, column: 7, scope: !16)
!20 = !{i1 false}
!21 = !DILocation(line: 558, column: 2, scope: !16)
!22 = !DILocation(line: 559, column: 4, scope: !16)
!23 = !DILocation(line: 560, column: 1, scope: !16)
!24 = distinct !DISubprogram(name: "free_g2", scope: !11, file: !11, line: 561, type: !17, scopeLine: 561, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !4)
!25 = !DILocation(line: 562, column: 6, scope: !26)
!26 = distinct !DILexicalBlock(scope: !24, file: !11, line: 562, column: 6)
!27 = !DILocation(line: 562, column: 8, scope: !26)
!28 = !DILocation(line: 562, column: 6, scope: !24)
!29 = !DILocation(line: 563, column: 9, scope: !26)
!30 = !DILocation(line: 563, column: 8, scope: !26)
!31 = !DILocation(line: 563, column: 3, scope: !26)
!32 = !DILocation(line: 564, column: 1, scope: !24)
!33 = distinct !DISubprogram(name: "h", scope: !11, file: !11, line: 565, type: !17, scopeLine: 565, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !4)
!34 = !DILocation(line: 566, column: 6, scope: !35)
!35 = distinct !DILexicalBlock(scope: !33, file: !11, line: 566, column: 6)
!36 = !{i1 true}
!37 = !DILocation(line: 566, column: 6, scope: !33)
!38 = !DILocation(line: 566, column: 32, scope: !35)
!39 = !DILocation(line: 567, column: 1, scope: !33)
!40 = distinct !DISubprogram(name: "main", scope: !11, file: !11, line: 573, type: !41, scopeLine: 573, spFlags: DISPFlagDefinition, unit: !2, retainedNodes: !4)
!41 = !DISubroutineType(types: !42)
!42 = !{!9}
!43 = !DILocation(line: 574, column: 15, scope: !40)
!44 = !DILocation(line: 574, column: 6, scope: !40)
!45 = !DILocation(line: 574, column: 4, scope: !40)
!46 = !DILocation(line: 575, column: 7, scope: !47)
!47 = distinct !DILexicalBlock(scope: !40, file: !11, line: 575, column: 7)
!48 = !DILocation(line: 575, column: 7, scope: !40)
!49 = !DILocation(line: 575, column: 33, scope: !47)
!50 = !DILocation(line: 577, column: 15, scope: !40)
!51 = !DILocation(line: 577, column: 7, scope: !40)
!52 = !DILocation(line: 577, column: 3, scope: !40)
!53 = !DILocation(line: 577, column: 5, scope: !40)
!54 = !DILocation(line: 578, column: 2, scope: !40)
!55 = !DILocation(line: 579, column: 8, scope: !40)
!56 = !DILocation(line: 579, column: 7, scope: !40)
!57 = !DILocation(line: 579, column: 2, scope: !40)
!58 = !DILocation(line: 580, column: 7, scope: !40)
!59 = !DILocation(line: 580, column: 2, scope: !40)
!60 = !DILocation(line: 581, column: 4, scope: !40)
!61 = !DILocation(line: 582, column: 2, scope: !40)
!62 = !DILocation(line: 583, column: 2, scope: !40)
