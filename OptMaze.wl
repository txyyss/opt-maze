(* ::Package:: *)

BeginPackage["OptMaze`"]


textImage::usage="textImage[text_String,imageSize_Integer:150,fontFamily_String:\"Helvetica\" ,padding_Integer:3]"


addBars::usage="addBars[img_,ppos_]:=ReplacePixelValue[img,ppos->0]"


vertCutImage::usage="vertCutImage[img_, {n1, n2, n3}]"


exportImage::usage="exportImage[name_,img_]"


exportImages::usage="exportImages[prefix_, imgs_]"


drawTile::usage="drawTile[{i_, j_, t_}]"


importSolution::usage="importSolution[filePrefix_String]"


importSolutions::usage="importSolutions[filePrefix_String, count_]"


horizontalJoin::usage="horizontalJoin[sols_]"


verticalJoin::usage="verticalJoin[sols_]"


exportSolutionMatrix::usage="exportSolutionMatrix[sols_, {width_, height_}]"


Begin["`Private`"]


textImage[text_String,imageSize_Integer:150,fontFamily_String:"Helvetica",padding_Integer:3]:=Binarize[ImagePad[ImageCrop[Rasterize[Style[text,FontFamily->fontFamily],RasterSize->imageSize]],padding,White]]


addBars[img_,ppos_]:=ReplacePixelValue[img,ppos->0]


cutRange[width_,cuts_]:={#[[1]],#[[2]]-1}&/@Partition[Append[Prepend[cuts,1],1+width],2,1]


vertCutImage[img_,cuts_]:=Module[{wh=ImageDimensions[img]},Map[ImageTake[img,All,#]&,cutRange[wh[[1]],cuts]]]


imageExpr[img_]:=StringRiffle[ImageData[img],"\n",""]


exportImage[name_,img_]:=Export[name<>".txt",imageExpr[img]]


exportImages[prefix_,imgs_]:=MapIndexed[Export[prefix<>ToString[First[#2]]<>".txt",imageExpr[#1]]&,imgs]


tilePattern={{{1,2},{1,1},{2,1}},{{1,0},{1,1},{2,1}},{{0,1},{1,1},{1,0}},{{0,1},{1,1},{1,2}},{{1,0},{1,2}},{{0,1},{2,1}},{{{1,0},{1,2}},{{0,1},{2,1}}}};


drawTile[{i_,j_,t_}]:={AbsoluteThickness[5],If[t<=7,Line[Map[{2(j-1),2(1-i)}+#&,tilePattern[[t]],{If[t<=6,1,2]}]]],AbsoluteThickness[0.5],Line[{{2(j-1),2(1-i)},{2j,2(1-i)},{2j,2(1-i)+2},{2j-2,2(1-i)+2},{2(j-1),2(1-i)}}]}


importSolution[filePrefix_String]:=DeleteCases[Get[filePrefix<>".out"],{_,_,8}]


importSolutions[filePrefix_String,count_]:=DeleteCases[Get[filePrefix<>ToString[#]<>".out"],{_,_,8}]&/@Table[i,{i,count}]


horizontalShift[sols_,offset_]:=Map[{0,offset,0}+#&,sols]


verticalShift[sols_,offset_]:=Map[{offset,0,0}+#&,sols]


joinSplitSols[sols_,joinFunc_,offsets_]:=Join@@MapThread[joinFunc,{sols,offsets}]


horizontalJoin[sols_]:=joinSplitSols[sols,horizontalShift,Most[FoldList[Plus,0,Map[Function[pts,Max[#[[2]]&/@pts]+1],sols]]]]


verticalJoin[sols_]:=joinSplitSols[sols,verticalShift,Most[FoldList[Plus,0,Map[Function[pts,Max[#[[1]]&/@pts]+1],sols]]]]


genSolutionMatrix[sols_,{width_,height_}]:=Module[{solMat},
solMat=Table[Table[8,width],height];
Scan[Set[solMat[[#[[1]]+1,#[[2]]+1]],#[[3]]]&,sols];
solMat]

matSExp[mat_]:=StringRiffle[mat,{"(","\n",")\n"},{"("," ",")"}]

exportSolutionMatrix[sols_,{width_,height_}]:=matSExp[genSolutionMatrix[sols,{width,height}]]

End[]


EndPackage[]
