; ModuleID = '/home/zhuyt/SESL/bin/b-zs0sozx8.bc'
source_filename = "llvm-link"
target datalayout = "e-m:e-p270:32:32-p271:32:32-p272:64:64-i64:64-f80:128-n8:16:32:64-S128"
target triple = "x86_64-pc-linux-gnu"

%struct.TLItem = type { %struct.TLItem*, %struct.DItem* }
%struct.DItem = type { %struct.DItem*, i32 }

@.str = private unnamed_addr constant [2 x i8] c"0\00", align 1
@.str.1 = private unnamed_addr constant [12 x i8] c"test-0513.c\00", align 1
@__PRETTY_FUNCTION__.reach_error = private unnamed_addr constant [19 x i8] c"void reach_error()\00", align 1

; Function Attrs: noinline nounwind uwtable
define internal void @reach_error() #0 !dbg !7 {
  call void @__assert_fail(i8* getelementptr inbounds ([2 x i8], [2 x i8]* @.str, i64 0, i64 0), i8* getelementptr inbounds ([12 x i8], [12 x i8]* @.str.1, i64 0, i64 0), i32 3, i8* getelementptr inbounds ([19 x i8], [19 x i8]* @__PRETTY_FUNCTION__.reach_error, i64 0, i64 0)) #5, !dbg !11, !verifier.code !14
  unreachable, !dbg !11, !verifier.code !14
}

; Function Attrs: noreturn nounwind
declare dso_local void @__assert_fail(i8*, i8*, i32, i8*) #1

; Function Attrs: noinline nounwind uwtable
define dso_local i32 @main() #0 !dbg !15 {
  call void @llvm.dbg.value(metadata %struct.TLItem* null, metadata !19, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %1 = call i32 @__VERIFIER_nondet_int(), !dbg !31, !verifier.code !32
  %2 = icmp ne i32 %1, 0, !dbg !33, !verifier.code !14
  br i1 %2, label %.lr.ph16, label %26, !dbg !33, !verifier.code !14

.lr.ph16:                                         ; preds = %0
  br label %3, !dbg !33, !verifier.code !14

3:                                                ; preds = %forwarder20, %.lr.ph16
  %.0114 = phi %struct.TLItem* [ null, %.lr.ph16 ], [ %.1, %forwarder20 ], !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.TLItem* %.0114, metadata !19, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %4 = call noalias i8* @malloc(i32 16) #6, !dbg !34, !verifier.code !14
  %5 = bitcast i8* %4 to %struct.DItem*, !dbg !34, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %5, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %6 = icmp ne %struct.DItem* %5, null, !dbg !37, !verifier.code !14
  br i1 %6, label %8, label %7, !dbg !39, !verifier.code !14

7:                                                ; preds = %3
  call void @abort() #5, !dbg !40, !verifier.code !14
  unreachable, !dbg !40, !verifier.code !14

8:                                                ; preds = %3
  %9 = getelementptr inbounds %struct.DItem, %struct.DItem* %5, i32 0, i32 0, !dbg !41, !verifier.code !14
  store %struct.DItem* null, %struct.DItem** %9, align 8, !dbg !42, !verifier.code !14
  %10 = call i32 @__VERIFIER_nondet_int(), !dbg !43, !verifier.code !32
  %11 = getelementptr inbounds %struct.DItem, %struct.DItem* %5, i32 0, i32 1, !dbg !44, !verifier.code !14
  store i32 %10, i32* %11, align 8, !dbg !45, !verifier.code !14
  %12 = call noalias i8* @malloc(i32 16) #6, !dbg !46, !verifier.code !14
  %13 = bitcast i8* %12 to %struct.TLItem*, !dbg !46, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.TLItem* %13, metadata !47, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %14 = icmp ne %struct.TLItem* %.0114, null, !dbg !48, !verifier.code !14
  br i1 %14, label %15, label %20, !dbg !50, !verifier.code !14

15:                                               ; preds = %8
  %16 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %.0114, i32 0, i32 0, !dbg !51, !verifier.code !14
  %17 = load %struct.TLItem*, %struct.TLItem** %16, align 8, !dbg !51, !verifier.code !14
  %18 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %13, i32 0, i32 0, !dbg !53, !verifier.code !14
  store %struct.TLItem* %17, %struct.TLItem** %18, align 8, !dbg !54, !verifier.code !14
  %19 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %.0114, i32 0, i32 0, !dbg !55, !verifier.code !14
  store %struct.TLItem* %13, %struct.TLItem** %19, align 8, !dbg !56, !verifier.code !14
  br label %22, !dbg !57, !verifier.code !14

20:                                               ; preds = %8
  %21 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %13, i32 0, i32 0, !dbg !58, !verifier.code !14
  store %struct.TLItem* %13, %struct.TLItem** %21, align 8, !dbg !60, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.TLItem* %13, metadata !19, metadata !DIExpression()), !dbg !30, !verifier.code !14
  br label %22, !verifier.code !14

22:                                               ; preds = %20, %15
  %.1 = phi %struct.TLItem* [ %.0114, %15 ], [ %13, %20 ], !dbg !30, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.TLItem* %.1, metadata !19, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %23 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %13, i32 0, i32 1, !dbg !61, !verifier.code !14
  store %struct.DItem* %5, %struct.DItem** %23, align 8, !dbg !62, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* null, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.TLItem* null, metadata !47, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %24 = call i32 @__VERIFIER_nondet_int(), !dbg !31, !verifier.code !32
  %25 = icmp ne i32 %24, 0, !dbg !33, !verifier.code !14
  br i1 %25, label %forwarder20, label %._crit_edge17, !dbg !33, !llvm.loop !63, !verifier.code !14

._crit_edge17:                                    ; preds = %22
  %split18 = phi %struct.TLItem* [ %.1, %22 ], !verifier.code !14
  br label %26, !dbg !33, !verifier.code !14

26:                                               ; preds = %._crit_edge17, %0
  %.01.lcssa = phi %struct.TLItem* [ %split18, %._crit_edge17 ], [ null, %0 ], !dbg !65, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.TLItem* %.01.lcssa, metadata !19, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %27 = icmp ne %struct.TLItem* %.01.lcssa, null, !dbg !66, !verifier.code !14
  br i1 %27, label %29, label %28, !dbg !68, !verifier.code !14

28:                                               ; preds = %26
  br label %92, !dbg !69, !verifier.code !14

29:                                               ; preds = %26
  call void @llvm.dbg.value(metadata %struct.TLItem* %.01.lcssa, metadata !19, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %30 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %.01.lcssa, i32 0, i32 0, !dbg !70, !verifier.code !14
  %31 = load %struct.TLItem*, %struct.TLItem** %30, align 8, !dbg !70, !verifier.code !14
  %32 = icmp ne %struct.TLItem* %31, %.01.lcssa, !dbg !71, !verifier.code !14
  br i1 %32, label %.lr.ph12, label %81, !dbg !72, !verifier.code !14

.lr.ph12:                                         ; preds = %29
  br label %33, !dbg !72, !verifier.code !14

33:                                               ; preds = %forwarder19, %.lr.ph12
  %.210 = phi %struct.TLItem* [ %.01.lcssa, %.lr.ph12 ], [ %77, %forwarder19 ], !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.TLItem* %.210, metadata !19, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %34 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %.210, i32 0, i32 1, !dbg !73, !verifier.code !14
  %35 = load %struct.DItem*, %struct.DItem** %34, align 8, !dbg !73, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %35, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %36 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %.210, i32 0, i32 0, !dbg !75, !verifier.code !14
  %37 = load %struct.TLItem*, %struct.TLItem** %36, align 8, !dbg !75, !verifier.code !14
  %38 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %37, i32 0, i32 1, !dbg !76, !verifier.code !14
  %39 = load %struct.DItem*, %struct.DItem** %38, align 8, !dbg !76, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %39, metadata !77, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %40 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %.210, i32 0, i32 0, !dbg !78, !verifier.code !14
  %41 = load %struct.TLItem*, %struct.TLItem** %40, align 8, !dbg !78, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.TLItem* %41, metadata !47, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %42 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %41, i32 0, i32 0, !dbg !79, !verifier.code !14
  %43 = load %struct.TLItem*, %struct.TLItem** %42, align 8, !dbg !79, !verifier.code !14
  %44 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %.210, i32 0, i32 0, !dbg !80, !verifier.code !14
  store %struct.TLItem* %43, %struct.TLItem** %44, align 8, !dbg !81, !verifier.code !14
  %45 = bitcast %struct.TLItem* %41 to i8*, !dbg !82, !verifier.code !14
  call void @free(i8* %45) #6, !dbg !83, !verifier.code !14
  %46 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %.210, i32 0, i32 1, !dbg !84, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem** %46, metadata !85, metadata !DIExpression()), !dbg !87, !verifier.code !14
  br label %47, !dbg !88, !verifier.code !14

47:                                               ; preds = %65, %33
  %.07 = phi %struct.DItem** [ %46, %33 ], [ %67, %65 ], !dbg !87, !verifier.code !14
  %.05 = phi %struct.DItem* [ %39, %33 ], [ %.16, %65 ], !dbg !89, !verifier.code !14
  %.02 = phi %struct.DItem* [ %35, %33 ], [ %.13, %65 ], !dbg !87, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %.02, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %.05, metadata !77, metadata !DIExpression()), !dbg !30, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem** %.07, metadata !85, metadata !DIExpression()), !dbg !87, !verifier.code !14
  %48 = icmp ne %struct.DItem* %.02, null, !dbg !90, !verifier.code !14
  br i1 %48, label %49, label %51, !dbg !91, !verifier.code !14

49:                                               ; preds = %47
  %50 = icmp ne %struct.DItem* %.05, null, !dbg !91, !verifier.code !14
  br label %51, !verifier.code !14

51:                                               ; preds = %49, %47
  %52 = phi i1 [ false, %47 ], [ %50, %49 ], !dbg !87, !verifier.code !14
  br i1 %52, label %53, label %68, !dbg !88, !verifier.code !14

53:                                               ; preds = %51
  %54 = getelementptr inbounds %struct.DItem, %struct.DItem* %.02, i32 0, i32 1, !dbg !92, !verifier.code !14
  %55 = load i32, i32* %54, align 8, !dbg !92, !verifier.code !14
  %56 = getelementptr inbounds %struct.DItem, %struct.DItem* %.05, i32 0, i32 1, !dbg !95, !verifier.code !14
  %57 = load i32, i32* %56, align 8, !dbg !95, !verifier.code !14
  %58 = icmp slt i32 %55, %57, !dbg !96, !verifier.code !14
  br i1 %58, label %59, label %62, !dbg !97, !verifier.code !14

59:                                               ; preds = %53
  store %struct.DItem* %.02, %struct.DItem** %.07, align 8, !dbg !98, !verifier.code !14
  %60 = getelementptr inbounds %struct.DItem, %struct.DItem* %.02, i32 0, i32 0, !dbg !100, !verifier.code !14
  %61 = load %struct.DItem*, %struct.DItem** %60, align 8, !dbg !100, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %61, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  br label %65, !dbg !101, !verifier.code !14

62:                                               ; preds = %53
  store %struct.DItem* %.05, %struct.DItem** %.07, align 8, !dbg !102, !verifier.code !14
  %63 = getelementptr inbounds %struct.DItem, %struct.DItem* %.05, i32 0, i32 0, !dbg !104, !verifier.code !14
  %64 = load %struct.DItem*, %struct.DItem** %63, align 8, !dbg !104, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %64, metadata !77, metadata !DIExpression()), !dbg !30, !verifier.code !14
  br label %65, !verifier.code !14

65:                                               ; preds = %62, %59
  %.16 = phi %struct.DItem* [ %.05, %59 ], [ %64, %62 ], !dbg !87, !verifier.code !14
  %.13 = phi %struct.DItem* [ %61, %59 ], [ %.02, %62 ], !dbg !87, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %.13, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %.16, metadata !77, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %66 = load %struct.DItem*, %struct.DItem** %.07, align 8, !dbg !105, !verifier.code !14
  %67 = getelementptr inbounds %struct.DItem, %struct.DItem* %66, i32 0, i32 0, !dbg !106, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem** %67, metadata !85, metadata !DIExpression()), !dbg !87, !verifier.code !14
  br label %47, !dbg !88, !llvm.loop !107, !verifier.code !14

68:                                               ; preds = %51
  %.07.lcssa = phi %struct.DItem** [ %.07, %51 ], !dbg !87, !verifier.code !14
  %.05.lcssa = phi %struct.DItem* [ %.05, %51 ], !dbg !89, !verifier.code !14
  %.02.lcssa = phi %struct.DItem* [ %.02, %51 ], !dbg !87, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem** %.07.lcssa, metadata !85, metadata !DIExpression()), !dbg !87, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %.05.lcssa, metadata !77, metadata !DIExpression()), !dbg !30, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %.02.lcssa, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %69 = icmp ne %struct.DItem* %.02.lcssa, null, !dbg !109, !verifier.code !14
  br i1 %69, label %70, label %71, !dbg !111, !verifier.code !14

70:                                               ; preds = %68
  store %struct.DItem* %.02.lcssa, %struct.DItem** %.07.lcssa, align 8, !dbg !112, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* null, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  br label %75, !dbg !114, !verifier.code !14

71:                                               ; preds = %68
  %72 = icmp ne %struct.DItem* %.05.lcssa, null, !dbg !115, !verifier.code !14
  br i1 %72, label %73, label %74, !dbg !117, !verifier.code !14

73:                                               ; preds = %71
  store %struct.DItem* %.05.lcssa, %struct.DItem** %.07.lcssa, align 8, !dbg !118, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* null, metadata !77, metadata !DIExpression()), !dbg !30, !verifier.code !14
  br label %74, !dbg !120, !verifier.code !14

74:                                               ; preds = %73, %71
  br label %75, !verifier.code !14

75:                                               ; preds = %74, %70
  call void @llvm.dbg.value(metadata %struct.DItem** null, metadata !85, metadata !DIExpression()), !dbg !87, !verifier.code !14
  %76 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %.210, i32 0, i32 0, !dbg !121, !verifier.code !14
  %77 = load %struct.TLItem*, %struct.TLItem** %76, align 8, !dbg !121, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.TLItem* %77, metadata !19, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %78 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %77, i32 0, i32 0, !dbg !70, !verifier.code !14
  %79 = load %struct.TLItem*, %struct.TLItem** %78, align 8, !dbg !70, !verifier.code !14
  %80 = icmp ne %struct.TLItem* %79, %77, !dbg !71, !verifier.code !14
  br i1 %80, label %forwarder19, label %._crit_edge13, !dbg !72, !llvm.loop !122, !verifier.code !14

._crit_edge13:                                    ; preds = %75
  %split = phi %struct.TLItem* [ %77, %75 ], !verifier.code !14
  br label %81, !dbg !72, !verifier.code !14

81:                                               ; preds = %._crit_edge13, %29
  %.2.lcssa = phi %struct.TLItem* [ %split, %._crit_edge13 ], [ %.01.lcssa, %29 ], !dbg !30, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.TLItem* %.2.lcssa, metadata !19, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %82 = getelementptr inbounds %struct.TLItem, %struct.TLItem* %.2.lcssa, i32 0, i32 1, !dbg !124, !verifier.code !14
  %83 = load %struct.DItem*, %struct.DItem** %82, align 8, !dbg !124, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %83, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %84 = bitcast %struct.TLItem* %.2.lcssa to i8*, !dbg !125, !verifier.code !14
  call void @free(i8* %84) #6, !dbg !126, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %83, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %85 = icmp ne %struct.DItem* %83, null, !dbg !127, !verifier.code !14
  br i1 %85, label %.lr.ph, label %91, !dbg !127, !verifier.code !14

.lr.ph:                                           ; preds = %81
  br label %86, !dbg !127, !verifier.code !14

86:                                               ; preds = %forwarder, %.lr.ph
  %.249 = phi %struct.DItem* [ %83, %.lr.ph ], [ %88, %forwarder ], !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %.249, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %.249, metadata !77, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %87 = getelementptr inbounds %struct.DItem, %struct.DItem* %.249, i32 0, i32 0, !dbg !128, !verifier.code !14
  %88 = load %struct.DItem*, %struct.DItem** %87, align 8, !dbg !128, !verifier.code !14
  call void @llvm.dbg.value(metadata %struct.DItem* %88, metadata !36, metadata !DIExpression()), !dbg !30, !verifier.code !14
  %89 = bitcast %struct.DItem* %.249 to i8*, !dbg !130, !verifier.code !14
  call void @free(i8* %89) #6, !dbg !131, !verifier.code !14
  %90 = icmp ne %struct.DItem* %88, null, !dbg !127, !verifier.code !14
  br i1 %90, label %forwarder, label %._crit_edge, !dbg !127, !llvm.loop !132, !verifier.code !14

._crit_edge:                                      ; preds = %86
  br label %91, !dbg !127, !verifier.code !14

91:                                               ; preds = %._crit_edge, %81
  br label %92, !dbg !134, !verifier.code !14

92:                                               ; preds = %91, %28
  ret i32 0, !dbg !135, !verifier.code !14

forwarder:                                        ; preds = %86
  br label %86, !verifier.code !14

forwarder19:                                      ; preds = %75
  br label %33, !verifier.code !14

forwarder20:                                      ; preds = %22
  br label %3, !verifier.code !14
}

; Function Attrs: nounwind readnone speculatable willreturn
declare void @llvm.dbg.declare(metadata, metadata, metadata) #2

declare dso_local i32 @__VERIFIER_nondet_int() #3

; Function Attrs: nounwind
declare dso_local noalias i8* @malloc(i32) #4

; Function Attrs: noreturn nounwind
declare dso_local void @abort() #1

; Function Attrs: nounwind
declare dso_local void @free(i8*) #4

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
!1 = !DIFile(filename: "/home/zhuyt/slhv_expr/source_codes/test-0513.i", directory: "/home/zhuyt/SESL/bin")
!2 = !{}
!3 = !{!"Ubuntu clang version 10.0.1-++20211003085942+ef32c611aa21-1~exp1~20211003090334.2"}
!4 = !{i32 7, !"Dwarf Version", i32 4}
!5 = !{i32 2, !"Debug Info Version", i32 3}
!6 = !{i32 1, !"wchar_size", i32 4}
!7 = distinct !DISubprogram(name: "reach_error", scope: !8, file: !8, line: 12, type: !9, scopeLine: 12, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!8 = !DIFile(filename: "slhv_expr/source_codes/test-0513.i", directory: "/home/zhuyt")
!9 = !DISubroutineType(types: !10)
!10 = !{null}
!11 = !DILocation(line: 12, column: 83, scope: !12)
!12 = distinct !DILexicalBlock(scope: !13, file: !8, line: 12, column: 73)
!13 = distinct !DILexicalBlock(scope: !7, file: !8, line: 12, column: 67)
!14 = !{i1 false}
!15 = distinct !DISubprogram(name: "main", scope: !8, file: !8, line: 532, type: !16, scopeLine: 532, spFlags: DISPFlagDefinition, unit: !0, retainedNodes: !2)
!16 = !DISubroutineType(types: !17)
!17 = !{!18}
!18 = !DIBasicType(name: "int", size: 32, encoding: DW_ATE_signed)
!19 = !DILocalVariable(name: "data", scope: !15, file: !8, line: 533, type: !20)
!20 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !21, size: 64)
!21 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "TLItem", file: !8, line: 528, size: 128, elements: !22)
!22 = !{!23, !24}
!23 = !DIDerivedType(tag: DW_TAG_member, name: "next", scope: !21, file: !8, line: 529, baseType: !20, size: 64)
!24 = !DIDerivedType(tag: DW_TAG_member, name: "data", scope: !21, file: !8, line: 530, baseType: !25, size: 64, offset: 64)
!25 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !26, size: 64)
!26 = distinct !DICompositeType(tag: DW_TAG_structure_type, name: "DItem", file: !8, line: 524, size: 128, elements: !27)
!27 = !{!28, !29}
!28 = !DIDerivedType(tag: DW_TAG_member, name: "next", scope: !26, file: !8, line: 525, baseType: !25, size: 64)
!29 = !DIDerivedType(tag: DW_TAG_member, name: "value", scope: !26, file: !8, line: 526, baseType: !18, size: 32, offset: 64)
!30 = !DILocation(line: 0, scope: !15)
!31 = !DILocation(line: 536, column: 12, scope: !15)
!32 = !{i1 true}
!33 = !DILocation(line: 536, column: 5, scope: !15)
!34 = !DILocation(line: 537, column: 16, scope: !35)
!35 = distinct !DILexicalBlock(scope: !15, file: !8, line: 536, column: 37)
!36 = !DILocalVariable(name: "item", scope: !15, file: !8, line: 534, type: !25)
!37 = !DILocation(line: 538, column: 14, scope: !38)
!38 = distinct !DILexicalBlock(scope: !35, file: !8, line: 538, column: 13)
!39 = !DILocation(line: 538, column: 13, scope: !35)
!40 = !DILocation(line: 539, column: 13, scope: !38)
!41 = !DILocation(line: 540, column: 15, scope: !35)
!42 = !DILocation(line: 540, column: 20, scope: !35)
!43 = !DILocation(line: 541, column: 23, scope: !35)
!44 = !DILocation(line: 541, column: 15, scope: !35)
!45 = !DILocation(line: 541, column: 21, scope: !35)
!46 = !DILocation(line: 542, column: 17, scope: !35)
!47 = !DILocalVariable(name: "lItem", scope: !15, file: !8, line: 535, type: !20)
!48 = !DILocation(line: 543, column: 13, scope: !49)
!49 = distinct !DILexicalBlock(scope: !35, file: !8, line: 543, column: 13)
!50 = !DILocation(line: 543, column: 13, scope: !35)
!51 = !DILocation(line: 544, column: 33, scope: !52)
!52 = distinct !DILexicalBlock(scope: !49, file: !8, line: 543, column: 19)
!53 = !DILocation(line: 544, column: 20, scope: !52)
!54 = !DILocation(line: 544, column: 25, scope: !52)
!55 = !DILocation(line: 545, column: 19, scope: !52)
!56 = !DILocation(line: 545, column: 24, scope: !52)
!57 = !DILocation(line: 546, column: 9, scope: !52)
!58 = !DILocation(line: 547, column: 20, scope: !59)
!59 = distinct !DILexicalBlock(scope: !49, file: !8, line: 546, column: 16)
!60 = !DILocation(line: 547, column: 25, scope: !59)
!61 = !DILocation(line: 550, column: 16, scope: !35)
!62 = !DILocation(line: 550, column: 21, scope: !35)
!63 = distinct !{!63, !33, !64}
!64 = !DILocation(line: 553, column: 5, scope: !15)
!65 = !DILocation(line: 533, column: 20, scope: !15)
!66 = !DILocation(line: 554, column: 10, scope: !67)
!67 = distinct !DILexicalBlock(scope: !15, file: !8, line: 554, column: 9)
!68 = !DILocation(line: 554, column: 9, scope: !15)
!69 = !DILocation(line: 555, column: 9, scope: !67)
!70 = !DILocation(line: 556, column: 18, scope: !15)
!71 = !DILocation(line: 556, column: 23, scope: !15)
!72 = !DILocation(line: 556, column: 5, scope: !15)
!73 = !DILocation(line: 557, column: 22, scope: !74)
!74 = distinct !DILexicalBlock(scope: !15, file: !8, line: 556, column: 32)
!75 = !DILocation(line: 558, column: 23, scope: !74)
!76 = !DILocation(line: 558, column: 29, scope: !74)
!77 = !DILocalVariable(name: "item2", scope: !15, file: !8, line: 534, type: !25)
!78 = !DILocation(line: 559, column: 23, scope: !74)
!79 = !DILocation(line: 560, column: 29, scope: !74)
!80 = !DILocation(line: 560, column: 15, scope: !74)
!81 = !DILocation(line: 560, column: 20, scope: !74)
!82 = !DILocation(line: 561, column: 14, scope: !74)
!83 = !DILocation(line: 561, column: 9, scope: !74)
!84 = !DILocation(line: 562, column: 37, scope: !74)
!85 = !DILocalVariable(name: "dst", scope: !74, file: !8, line: 562, type: !86)
!86 = !DIDerivedType(tag: DW_TAG_pointer_type, baseType: !25, size: 64)
!87 = !DILocation(line: 0, scope: !74)
!88 = !DILocation(line: 563, column: 9, scope: !74)
!89 = !DILocation(line: 558, column: 15, scope: !74)
!90 = !DILocation(line: 563, column: 16, scope: !74)
!91 = !DILocation(line: 563, column: 21, scope: !74)
!92 = !DILocation(line: 564, column: 23, scope: !93)
!93 = distinct !DILexicalBlock(scope: !94, file: !8, line: 564, column: 17)
!94 = distinct !DILexicalBlock(scope: !74, file: !8, line: 563, column: 31)
!95 = !DILocation(line: 564, column: 38, scope: !93)
!96 = !DILocation(line: 564, column: 29, scope: !93)
!97 = !DILocation(line: 564, column: 17, scope: !94)
!98 = !DILocation(line: 565, column: 22, scope: !99)
!99 = distinct !DILexicalBlock(scope: !93, file: !8, line: 564, column: 45)
!100 = !DILocation(line: 566, column: 30, scope: !99)
!101 = !DILocation(line: 567, column: 13, scope: !99)
!102 = !DILocation(line: 568, column: 22, scope: !103)
!103 = distinct !DILexicalBlock(scope: !93, file: !8, line: 567, column: 20)
!104 = !DILocation(line: 569, column: 32, scope: !103)
!105 = !DILocation(line: 571, column: 21, scope: !94)
!106 = !DILocation(line: 571, column: 28, scope: !94)
!107 = distinct !{!107, !88, !108}
!108 = !DILocation(line: 572, column: 9, scope: !74)
!109 = !DILocation(line: 573, column: 13, scope: !110)
!110 = distinct !DILexicalBlock(scope: !74, file: !8, line: 573, column: 13)
!111 = !DILocation(line: 573, column: 13, scope: !74)
!112 = !DILocation(line: 574, column: 18, scope: !113)
!113 = distinct !DILexicalBlock(scope: !110, file: !8, line: 573, column: 19)
!114 = !DILocation(line: 576, column: 9, scope: !113)
!115 = !DILocation(line: 576, column: 20, scope: !116)
!116 = distinct !DILexicalBlock(scope: !110, file: !8, line: 576, column: 20)
!117 = !DILocation(line: 576, column: 20, scope: !110)
!118 = !DILocation(line: 577, column: 18, scope: !119)
!119 = distinct !DILexicalBlock(scope: !116, file: !8, line: 576, column: 27)
!120 = !DILocation(line: 579, column: 9, scope: !119)
!121 = !DILocation(line: 581, column: 22, scope: !74)
!122 = distinct !{!122, !72, !123}
!123 = !DILocation(line: 582, column: 5, scope: !15)
!124 = !DILocation(line: 583, column: 18, scope: !15)
!125 = !DILocation(line: 584, column: 10, scope: !15)
!126 = !DILocation(line: 584, column: 5, scope: !15)
!127 = !DILocation(line: 585, column: 5, scope: !15)
!128 = !DILocation(line: 587, column: 22, scope: !129)
!129 = distinct !DILexicalBlock(scope: !15, file: !8, line: 585, column: 18)
!130 = !DILocation(line: 588, column: 14, scope: !129)
!131 = !DILocation(line: 588, column: 9, scope: !129)
!132 = distinct !{!132, !127, !133}
!133 = !DILocation(line: 589, column: 5, scope: !15)
!134 = !DILocation(line: 590, column: 5, scope: !15)
!135 = !DILocation(line: 591, column: 1, scope: !15)
