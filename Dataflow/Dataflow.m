
BeginPackage["Dataflow`Dataflow`"] 

ClearAll[
	Dataflow,
	ToBasicBlocks,
	BasicBlock,
	Instruction
]

Begin["`Private`"]


(*************************************************************************)
(*************************************************************************)

Dataflow[] :=
	{}

(*************************************************************************)
(*************************************************************************)
(*************************************************************************)
(*** Basic Instruction Lowering                                       ****)
(*************************************************************************)
(*************************************************************************)
(*************************************************************************)

SetAttributes[ToBasicBlocks, {HoldAllComplete}]
ToBasicBlocks[stmts0__] :=
	Module[{state, stmts = Inactivate[stmts0]},
		state["counter"] = 0;
		state["basicBlocks"] = Association[];
		state["basicBlockOrder"] = {};
		state["currentBB"] = "start";
		newBasicBlock[state, "start"];
		lower[state, stmts];
		BasicBlock[#, state["basicBlocks"][#]]& /@ state["basicBlockOrder"]
	]

ClearAll[lower]	
lower[state_, stmt:(Inactive[CompoundExpression][args___])] :=
	 lower[state, #]& /@ {args}
	 
lower[state_, stmt:(Inactive[While][cond_, body_])] :=
	Module[{condV, bodyLbl, endLbl},
		bodyLbl = makeLabel[];
		endLbl = makeLabel[];
		newBasicBlock[state, bodyLbl];
		condV = lower[state, cond];
		addStatement[state, Instruction["Branch", {condV, bodyLbl, endLbl}]];
		lower[state, body];
		addStatement[state, Instruction["Jump", bodyLbl]];
		newBasicBlock[state, endLbl]
	]
	 
lower[state_, stmt:(Inactive[If][cond_, then_, else_])] :=
	Module[{thenLbl, elseLbl, endLbl, condV, currBB},
		thenLbl = makeLabel[];
		elseLbl = makeLabel[];
		endLbl = makeLabel[];
		currBB = state["currentBB"];
		condV = lower[state, cond];
		addStatement[state, Instruction["Branch", {condV, thenLbl, elseLbl}]];
		(* then *)
			newBasicBlock[state, thenLbl];
			lower[state, then];
			addStatement[state, Instruction["Branch", endLbl]];
		(* else *)
			newBasicBlock[state, elseLbl];
			lower[state, else];
			addStatement[state, Instruction["Branch", endLbl]];
		newBasicBlock[state, endLbl]
	]
	
lower[state_, stmt:(Inactive[Set][lhs0_, rhs0_])] :=
	Module[{lhs, rhs},
		rhs = lower[state, rhs0];
		lhs = lower[state, lhs0];
		addStatement[state, Instruction["Set", {lhs, rhs}]]
	] 

lower[state_, Null] :=
	Sequence[]
	
(*************************************************************************)
(*************************************************************************)

ClearAll[binaryOp]
binaryOp[Plus | Minus | Divide] = True
binaryOp[___] := False

ClearAll[cmpOp]
cmpOp[Equal | Less | Greater | LessEqual | GreaterEqual] = True
cmpOp[___] := False

lower[state_, Inactive[op_?cmpOp][lhs0_, rhs0_]] :=
	Module[{lhs, rhs, newVar},
		lhs = lower[state, lhs0];
		rhs = lower[state, rhs0];
		newVar = makeVar[];
		addStatement[state, Instruction["Set", {newVar, Instruction["Compare", {op, lhs, rhs}]}]];
		newVar
	]
	
lower[state_, any_] :=
	any

newBasicBlock[state_, bb_] :=
	Module[{assoc},
		AppendTo[state["basicBlockOrder"], bb];
		state["currentBB"] = bb;
		assoc = state["basicBlocks"];
		assoc[bb] = {Instruction["Label", bb]};
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

ClearAll[bbCounter]
bbCounter = 0

(*************************************************************************)

ClearAll[varCounter]
varCounter = 0

(*************************************************************************)

makeVar[] := "var" <> ToString[varCounter++]
makeLabel[] := "bb" <> ToString[bbCounter++]

(*************************************************************************)
(*************************************************************************)


End[]

EndPackage[]

