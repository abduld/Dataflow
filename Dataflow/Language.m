
BeginPackage["Dataflow`Language`"]

BasicBlock;
Instruction;
TranslateNotation;

Begin["`Private`"]

(* This language in based on steeensgard's paper
   with some modifications needed for Andersen *)

$OpCodes = {
	"Label",
	"Set",
	"BinaryOp"
};


TranslateNotation["lbl:"] :=
	Instruction["Label", "lbl"]
TranslateNotation["x = y"] :=
	Instruction["Set", {"x", "y"}];
TranslateNotation["op(y_0, ..., y_n)"] :=
	Instruction["BinaryOp", {"op", "ys"}];

End[]

EndPackage[]

