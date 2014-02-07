
BeginPackage["Dataflow`Dataflow`"] 

ClearAll[
	Dataflow,
	ToBasicBlocks,
	ToControlFlowDiagram,
	BasicBlock,
	Instruction,
	PreOrderVertexList,
	ReversePreOrderVertexList,
	PostOrderVertexList,
	ReversePostOrderScan
]

Begin["`Private`"]


(*************************************************************************)
(*************************************************************************)

Dataflow[] :=
	{}

(* Def-Use Chain *)

(* Use-Def Chain *)

(* Reaching Definitions *)

(* *)


uses[Instruction[n_, Set, {_, r___}]] := uses /@ {r}  
kill[Instruction[_, Set, {x_, ___}]] := x

PreOrderVertexList[g_] :=
	Module[{state},
		state["visited"] = {};
		DeleteDuplicates[iPreOrderVertexList[g, "start", state]]
	]
iPreOrderVertexList[g_, root_, state_] :=
	Module[{},
		AppendTo[state["visited"], root];
		Flatten[{
			root,
			iPreOrderVertexList[g, #, state]& /@ Select[Last /@ EdgeList[g, DirectedEdge[root, _]], FreeQ[state["visited"], #]&]
		}]
	]
		 
ReversePreOrderVertexList[g_] := Reverse[PreOrderVertexList[g]]

PostOrderVertexList[g_] :=
	Module[{state},
		state["visited"] = {};
		DeleteDuplicates[iPostOrderVertexList[g, "start", state]]
	]
iPostOrderVertexList[g_, root_, state_] :=
	Module[{},
		AppendTo[state["visited"], root];
		Flatten[{
			iPostOrderVertexList[g, #, state]& /@ Select[Last /@ EdgeList[g, DirectedEdge[root, _]], FreeQ[state["visited"], #]&],
			root
		}]
	]
	
ReversePostOrderScan[g_] := Reverse[PostOrderVertexList[g]]

(*************************************************************************)
(*************************************************************************)
(*** Monotone Framework                                               ****)
(*************************************************************************)
(*************************************************************************)




(*************************************************************************)
(*************************************************************************)
(*************************************************************************)
(*** Basic Instruction Lowering & CFG Construction                    ****)
(*************************************************************************)
(*************************************************************************)
(*************************************************************************)

SetAttributes[ToBasicBlocks, {HoldAllComplete}]
(* Examples:
	ToBasicBlocks[
		While[x == 1, x = 1];
		j = 1;
		If[x == 1, x = 1, y = 1];
	]
*)
ToBasicBlocks[stmts__] :=
	doLowering[stmts]["BasicBlocks"]
	
SetAttributes[ToControlFlowDiagram, {HoldAllComplete}]
(* Examples:
	ToControlFlowDiagram[
		While[x == 1, x = 1];
		j = 1;
		If[x == 1, x = 1, y = 1];
	]
*)
ToControlFlowDiagram[stmts__] :=
	doLowering[stmts]["ControlFlowDiagram"]
	
SetAttributes[doLowering, {HoldAllComplete}]
doLowering[stmts0__] :=
	Module[{state, stmts = Inactivate[stmts0], bbs, cfg},
		bbCounter = 0;
		varCounter = 0;
		state["instructionCounter"] = 0;
		state["basicBlocks"] = Association[];
		state["basicBlockOrder"] = {};
		state["currentBB"] = "start";
		state["controlFlow"] = {};
		newBasicBlock[state, "start"];
		lower[state, stmts];
		bbs = BasicBlock[#, state["basicBlocks"][#]]& /@ state["basicBlockOrder"];
		cfg = Graph[
			MapThread[
				Tooltip[Property[#1, "BasicBlock" -> #2], #2]&,
				{state["basicBlockOrder"], bbs}
			],
			state["controlFlow"],
			VertexLabels -> "Name"
		];
		<|
			"ControlFlowDiagram" -> cfg,
			"BasicBlocks" -> bbs
		|>
	]

ClearAll[lower]	
lower[state_, stmt:(Inactive[CompoundExpression][args___])] :=
	 lower[state, #]& /@ {args}
	 
lower[state_, stmt:(Inactive[While][cond_, body_])] :=
	Module[{condV, bodyLbl, endLbl},
		bodyLbl = makeLabel[];
		endLbl = makeLabel[];
		addContolFlowEdge[state, state["currentBB"], bodyLbl];
		addContolFlowEdge[state, bodyLbl, bodyLbl];
		addContolFlowEdge[state, bodyLbl, endLbl];
		newBasicBlock[state, bodyLbl];
		condV = lower[state, cond];
		addStatement[state, newInstruction[state, "Branch", {condV, bodyLbl, endLbl}]];
		lower[state, body];
		addStatement[state, newInstruction[state, "Jump", bodyLbl]];
		newBasicBlock[state, endLbl]
	]
	 
lower[state_, stmt:(Inactive[If][cond_, then_, else_])] :=
	Module[{thenLbl, elseLbl, endLbl, condV, currBB},
		thenLbl = makeLabel[];
		elseLbl = makeLabel[];
		endLbl = makeLabel[];
		currBB = state["currentBB"];
		addContolFlowEdge[state, currBB, thenLbl];
		addContolFlowEdge[state, currBB, elseLbl];
		addContolFlowEdge[state, thenLbl, endLbl];
		addContolFlowEdge[state, elseLbl, endLbl];
		condV = lower[state, cond];
		addStatement[state, newInstruction[state, "Branch", {condV, thenLbl, elseLbl}]];
		(* then *)
			newBasicBlock[state, thenLbl];
			lower[state, then];
			addStatement[state, newInstruction[state, "Branch", endLbl]];
		(* else *)
			newBasicBlock[state, elseLbl];
			lower[state, else];
			addStatement[state, newInstruction[state, "Branch", endLbl]];
		newBasicBlock[state, endLbl]
	]
	
lower[state_, stmt:(Inactive[Set][lhs0_, rhs0_])] :=
	Module[{lhs, rhs},
		rhs = lower[state, rhs0];
		lhs = lower[state, lhs0];
		addStatement[state, newInstruction[state, "Set", {lhs, rhs}]]
	] 

lower[state_, Null] :=
	Sequence[]
	
(*************************************************************************)
(*************************************************************************)

ClearAll[binaryOp]
binaryOp[Plus | Minus | Divide] = True
binaryOp[Equal | Less | Greater | LessEqual | GreaterEqual] = True
binaryOp[___] := False
	
lower[state_, Inactive[op_?binaryOp][lhs0_, rhs0_]] :=
	Module[{lhs, rhs, newVar},
		lhs = lower[state, lhs0];
		rhs = lower[state, rhs0];
		newVar = makeVar[];
		addStatement[state, newInstruction[state, "Set", {newVar, Instruction[op, {lhs, rhs}]}]];
		newVar
	]
	
lower[state_, any_] :=
	any

newBasicBlock[state_, bb_] :=
	Module[{assoc},
		AppendTo[state["basicBlockOrder"], bb];
		state["currentBB"] = bb;
		assoc = state["basicBlocks"];
		assoc[bb] = {newInstruction[state, "Label", bb]};
		state["basicBlocks"] = assoc
	]
	
addStatement[state_, stmt_] :=
	addToBasicBlock[state, state["currentBB"], stmt]
addToBasicBlock[state_, bb_, stmt_] :=
	Module[{assoc},
		state["currentBB"] = bb;
		assoc = state["basicBlocks"];
		assoc[bb] = Flatten[{state["basicBlocks"][bb], stmt}];
		state["basicBlocks"] = assoc;
		stmt
	]
	
(*************************************************************************)

newInstruction[state_, args___] :=
	Instruction[state["instructionCounter"]++, args]

(*************************************************************************)


addContolFlowEdge[state_, from_, to_] :=
	AppendTo[state["controlFlow"], DirectedEdge[from, to]]

ClearAll[bbCounter]
bbCounter = 0
makeVar[] := "var" <> ToString[varCounter++]

ClearAll[varCounter]
varCounter = 0
makeLabel[] := "bb" <> ToString[bbCounter++]

(*************************************************************************)
(*************************************************************************)


End[]

EndPackage[]

