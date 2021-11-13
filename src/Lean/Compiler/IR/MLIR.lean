import Init.Data.String
import Init.Data.String.Basic
import Init.Data.Char.Basic
import Init.System.IO
import Lean.Parser
import Lean.Parser.Extra
import Init.System.Platform
import Init.Data.String.Basic
import Init.Data.Repr
import Init.Data.ToString.Basic

open Lean PrettyPrinter
-- === DOC
-- === DOC
-- === DOC
-- === DOC
-- === DOC

namespace MLIR.Doc

inductive Doc : Type where
  | Concat : Doc -> Doc -> Doc
  | Nest : Doc -> Doc
  | VGroup : List Doc -> Doc
  | Text: String -> Doc


class Pretty (a : Type) where
  doc : a -> Doc

open Pretty

def vgroup [Pretty a] (as: List a): Doc :=
  Doc.VGroup (as.map doc)

def nest_vgroup [Pretty a] (as: List a): Doc :=
  Doc.Nest (vgroup as)


instance : Pretty Doc where
  doc (d: Doc) := d

instance : Pretty String where
  doc := Doc.Text

instance : Pretty Int where
  doc := Doc.Text ∘ toString

instance : Pretty Char where
  doc := Doc.Text ∘ toString

instance : Inhabited Doc where
  default := Doc.Text ""


instance : Coe String Doc where
  coe := Doc.Text

instance : Append Doc where 
  append := Doc.Concat

instance : HAppend Doc String Doc where 
  hAppend (d: Doc) (s: String) := d ++ (doc s)

instance : HAppend String Doc Doc where 
  hAppend (s: String) (d: Doc) := (doc s) ++ d

def doc_dbl_quot : Doc :=  doc '"'

def doc_surround_dbl_quot [Pretty a] (v: a): Doc := 
    doc_dbl_quot ++ doc v ++ doc_dbl_quot
  

def doc_concat (ds: List Doc): Doc := ds.foldl Doc.Concat (Doc.Text "") 

partial def intercalate_doc_rec_ [Pretty d] (ds: List d) (i: Doc): Doc :=
  match ds with
  | [] => Doc.Text ""
  | (d::ds) => i ++ (doc d) ++ intercalate_doc_rec_ ds i

partial def  intercalate_doc [Pretty d] (ds: List d) (i: Doc): Doc := match ds with
 | [] => Doc.Text ""
 | [d] => doc d
 | (d::ds) => (doc d) ++ intercalate_doc_rec_ ds i


partial def layout 
  (d: Doc)
  (indent: Int) -- indent
  (width: Int) -- width
  (leftover: Int) -- characters left
  (newline: Bool) -- create newline?
  : String :=
  match d with
    | (Doc.Text s)  => (if newline then "\n".pushn ' ' indent.toNat else "") ++ s
    | (Doc.Concat d1 d2) =>
         let s := layout d1 indent width leftover newline
         s ++ layout d2 indent width (leftover - (s.length + 1)) false
    | (Doc.Nest d) => layout d (indent+1) width leftover newline
    | (Doc.VGroup ds) => 
       let ssInline := layout (doc_concat ds) indent width leftover newline 
       if false then ssInline -- ssInline.length <= leftover then ssInline
       else  
         let width' := width - indent
         -- TODO: don't make 
         String.join (ds.map (fun d => layout d indent width width True))


def layout80col (d: Doc) : String := layout d 0 80 0 false

instance : Coe Doc String where
   coe := layout80col

end MLIR.Doc

-- open MLIR.Doc
-- open Pretty -- open typeclass for `doc`

namespace MLIR.AST
open MLIR.Doc
open Pretty
-- EMBEDDING
-- ==========

inductive BBName
| mk: String -> BBName

instance : Pretty BBName where
  doc name := match name with 
              | BBName.mk s => "^" ++ doc s

mutual
inductive MLIRTy : Type where
| fn : MLIRTy -> MLIRTy -> MLIRTy
| int : Int -> MLIRTy
| tuple : List MLIRTy -> MLIRTy
| vector: Int -> MLIRTy -> MLIRTy

inductive SSAVal : Type where
  | SSAVal : String -> SSAVal

inductive AttrVal : Type where
| str : String -> AttrVal
| int : Int -> MLIRTy -> AttrVal
| type :MLIRTy -> AttrVal
| dense: Int -> MLIRTy -> AttrVal -- dense<10> : vector<i32>

inductive Attr : Type where
  | mk: (key: String) 
      -> (value: AttrVal)
      -> Attr

inductive Op : Type where 
 | mk: (name: String) 
      -> (args: List SSAVal)
      -> (bbs: List BBName)
      -> (regions: List Region) 
      -> (attrs: List Attr)
      -> (ty: MLIRTy)
      -> Op

inductive Path : Type where 
 | PathComponent: (regionix : Int) 
    -> (bbix: Int) 
    -> (opix: Int)
    -> (rec: Path)
    -> Path
 | Path

inductive BasicBlockStmt : Type where
| StmtAssign : SSAVal -> Op -> BasicBlockStmt
| StmtOp : Op -> BasicBlockStmt


inductive BasicBlock: Type where
| mk: (name: String) -> (args: List (SSAVal × MLIRTy)) -> (ops: List BasicBlockStmt) -> BasicBlock




inductive Region: Type where
| mk: (bbs: List BasicBlock) -> Region
end


partial instance :  Pretty MLIRTy where
  doc (ty: MLIRTy) :=
    let rec  go (ty: MLIRTy) :=  
    match ty with
    | MLIRTy.int k => "i" ++ doc k
    | MLIRTy.tuple ts => "(" ++ (intercalate_doc (ts.map go) (doc ", ") ) ++ ")"
    | MLIRTy.fn dom codom => (go dom) ++ " -> " ++ (go codom)
    | MLIRTy.vector sz ty => "vector<" ++ toString sz ++ "x" ++ go ty ++ ">"
    go ty



instance : Pretty AttrVal where
 doc (v: AttrVal) := 
   match v with
   | AttrVal.str str => doc_surround_dbl_quot str 
   | AttrVal.type ty => doc ty
   | AttrVal.int i ty => doc i ++ " : " ++ doc ty
   | AttrVal.dense i ty => "dense<" ++ doc i ++ ">" ++ ":" ++ doc ty


instance : Pretty Attr where
  doc (attr: Attr) := 
    match attr with
    | Attr.mk k v => k ++ " = " ++ (doc v)





instance : Pretty SSAVal where
   doc (val: SSAVal) := 
     match val with
     | SSAVal.SSAVal name => Doc.Text ("%" ++ name)



instance : ToFormat SSAVal where
    format (x: SSAVal) := layout80col (doc x)



-- | TODO: add a typeclass `Pretty` for things that can be converted to `Doc`.
mutual
partial def op_to_doc (op: Op): Doc := 
    match op with
    | (Op.mk name args bbs rgns attrs ty) => 
        let doc_name := doc_surround_dbl_quot name 
        let doc_bbs := if bbs.isEmpty
                       then doc ""
                       else "[" ++ intercalate_doc bbs ", " ++ "]"
        let doc_rgns := 
            if rgns.isEmpty
            then Doc.Text ""
            else " (" ++ nest_vgroup (rgns.map rgn_to_doc) ++ ")"
        let doc_args := "(" ++ intercalate_doc args ", " ++ ")"
        let doc_attrs :=
          if List.isEmpty attrs
          then Doc.Text ""
          else "{" ++ intercalate_doc attrs  ", " ++ "}"
        doc_name ++ doc_args ++  doc_bbs ++ doc_rgns ++ doc_attrs ++ " : " ++ doc ty

partial def bb_stmt_to_doc (stmt: BasicBlockStmt): Doc :=
  match stmt with
  | BasicBlockStmt.StmtAssign lhs rhs => (doc lhs) ++ " = " ++ (op_to_doc rhs)
  | BasicBlockStmt.StmtOp rhs => (op_to_doc rhs)

partial def bb_to_doc(bb: BasicBlock): Doc :=
  match bb with
  | (BasicBlock.mk name args stmts) => 
     let doc_arg (arg: SSAVal × MLIRTy) := 
        match arg with
        | (ssaval, ty) => doc ssaval ++ ":" ++ doc ty
     let bbargs := 
        if args.isEmpty then Doc.Text ""
        else "(" ++ 
             (intercalate_doc (args.map doc_arg) ", ") ++ 
             ")"
     let bbname := "^" ++ name ++ bbargs ++ ":"
     let bbbody := Doc.Nest (Doc.VGroup (stmts.map bb_stmt_to_doc))
     Doc.VGroup [bbname, bbbody]

partial def rgn_to_doc(rgn: Region): Doc :=
  match rgn with
  | (Region.mk bbs) => "{" ++ Doc.VGroup [nest_vgroup (bbs.map bb_to_doc), "}"]
 
end

instance : Pretty Op where
  doc := op_to_doc

instance : Pretty BasicBlockStmt where
  doc := bb_stmt_to_doc

instance : Pretty BasicBlock where
  doc := bb_to_doc

instance : Pretty Region where
  doc := rgn_to_doc

instance [Pretty a] : ToString a where
  toString (v: a) := layout80col (doc v)

instance : ToFormat Op where
    format (x: Op) := layout80col (doc x)


instance : Inhabited Op where
  default := Op.mk "INHABITANT" [] [] [] [] (MLIRTy.tuple [])


end MLIR.AST

namespace MLIR.EDSL
-- import MLIR.AST
-- import Lean.Parser
-- import Lean.Parser.Extra
-- import Lean.Init.Meta

open Lean
open Lean.Parser

open MLIR.AST

-- namespace MLIR.EDSL
-- EDSL
-- ====

declare_syntax_cat mlir_bb
declare_syntax_cat mlir_region
declare_syntax_cat mlir_bb_stmt
declare_syntax_cat mlir_op_results
declare_syntax_cat mlir_op
declare_syntax_cat mlir_op_args
declare_syntax_cat mlir_op_successor_args
declare_syntax_cat mlir_op_type
declare_syntax_cat mlir_op_operand
declare_syntax_cat mlir_type


-- syntax strLit mlir_op_args ":" mlir_op_type : mlir_op -- no region
-- 


-- EDSL OPERANDS
-- ==============

syntax "<[" term "]>" : mlir_op_operand
syntax "%" ident : mlir_op_operand
syntax "{{" term "}}" : mlir_op_operand

syntax "[mlir_op_operand| " mlir_op_operand "]" : term -- translate operands into term
macro_rules
  | `([mlir_op_operand| % $x:ident]) => `(SSAVal.SSAVal $(Lean.quote (toString x.getId))) 
  | `([mlir_op_operand| <[ $t:term ]> ]) => t
  | `([mlir_op_operand| {{ $t:term }} ]) => t

def xx := ([mlir_op_operand| %x])
def xxx := ([mlir_op_operand| %x])
#print xx
#print xxx


-- EDSL OP-SUCCESSOR-ARGS
-- =================

-- successor-list       ::= `[` successor (`,` successor)* `]`
-- successor            ::= caret-id (`:` bb-arg-list)?

declare_syntax_cat mlir_op_successor_arg -- bb argument
syntax "^" ident : mlir_op_successor_arg -- bb argument with no operands
-- syntax "^" ident ":" "(" mlir_op_operand","* ")" : mlir_op_successor_arg

syntax "[mlir_op_successor_arg|" mlir_op_successor_arg "]" : term

macro_rules
  | `([mlir_op_successor_arg| ^ $x:ident  ]) => 
      `(BBName.mk $(Lean.quote (toString x.getId)))

def succ0 :  BBName := ([mlir_op_successor_arg| ^bb])
#print succ0


-- EDSL MLIR TYPES
-- ===============

syntax "(" ")" : mlir_type
syntax "(" mlir_type ")" : mlir_type
syntax "(" mlir_type "," mlir_type ")" : mlir_type
syntax mlir_type "->" mlir_type : mlir_type
syntax "{{" term "}}" : mlir_type
syntax ident: mlir_type

-- | TODO: fix this rule, it interfers with way too much other stuff!
-- syntax "i" numLit : mlir_type

syntax "[mlir_type|" mlir_type "]" : term

macro_rules
  | `([mlir_type| $x:ident ]) => do
        let xstr := x.getId.toString
        if xstr.front == 'i'
        then do 
          let xstr' := xstr.drop 1
          match xstr'.toInt? with
          | some i => 
            let lit := Lean.Syntax.mkNumLit xstr'
            `(MLIRTy.int $lit)
          | none => 
              Macro.throwError $ "cannot convert suffix of i to int: " ++ xstr
        else Macro.throwError "expected i<int>" -- `(MLIRTy.int 1337)

def tyi32NoGap : MLIRTy := [mlir_type| i32] -- TODO: how to keep no gap?


macro_rules
| `([mlir_type| {{ $t }} ]) => t -- antiquot type

macro_rules
  | `([mlir_type| ( ) ]) => `(MLIRTy.tuple [])
  | `([mlir_type| ( $x:mlir_type )]) => 
        `(MLIRTy.tuple [ [mlir_type|$x] ])
  | `([mlir_type| ( $x:mlir_type, $y:mlir_type )]) => 
    `(MLIRTy.tuple [ [mlir_type|$x], [mlir_type|$y] ] )
  -- | `([mlir_type| i $x:numLit ) => `(MLIRTy.int $x)
  | `([mlir_type| $dom:mlir_type -> $codom:mlir_type]) =>
     `(MLIRTy.fn [mlir_type|$dom] [mlir_type|$codom])

def ty0 : MLIRTy := [mlir_type| ()]
def tyi32 : MLIRTy := [mlir_type| i32] -- TODO: how to keep no gap?
-- def tyi32' : MLIRTy := ([mlir_type| i32) -- TODO: how to keep no gap?
def tysingle : MLIRTy := [mlir_type| (i42)]
def typair : MLIRTy := [mlir_type| (i32, i64)]
def tyfn0 : MLIRTy := [mlir_type| () -> ()]
def tyfn1 : MLIRTy := [mlir_type| (i11) -> (i12)]
def tyfn2 : MLIRTy := [mlir_type| (i21, i22) -> (i23, i24)]
#print ty0
#print tyi32
#print typair
#print tyfn0
#print tyfn1
-- #print tyi32'


-- EDSL MLIR OP CALL, MLIR BB STMT
-- ===============================

-- syntax strLit mlir_op_args ":" mlir_type : mlir_op

syntax "[mlir_op|" mlir_op "]" : term


syntax mlir_op: mlir_bb_stmt
syntax mlir_op_operand "=" mlir_op : mlir_bb_stmt
syntax "{{" term "}}" : mlir_bb_stmt

syntax "[mlir_bb_stmt|" mlir_bb_stmt "]" : term


macro_rules
  | `([mlir_bb_stmt| $call:mlir_op ]) =>
       `(BasicBlockStmt.StmtOp ([mlir_op| $call]))
  | `([mlir_bb_stmt| $res:mlir_op_operand = $call:mlir_op]) => 
       `(BasicBlockStmt.StmtAssign ([mlir_op_operand| $res]) ([mlir_op| $call]))
  | `([mlir_bb_stmt| {{ $t }} ]) => t




-- EDSL MLIR BASIC BLOCK OPERANDS
-- ==============================

declare_syntax_cat mlir_bb_operand
syntax mlir_op_operand ":" mlir_type : mlir_bb_operand

syntax "mlir_bb_operand%" mlir_bb_operand : term

macro_rules 
| `(mlir_bb_operand% $name:mlir_op_operand : $ty:mlir_type ) => 
     `( ([mlir_op_operand| $name], [mlir_type|$ty]) ) 



-- EDSL MLIR BASIC BLOCKS
-- ======================


syntax "^" ident ":" (ws mlir_bb_stmt ws)* : mlir_bb
syntax "^" ident "(" sepBy(mlir_bb_operand, ",") ")" ":" (ws mlir_bb_stmt ws)* : mlir_bb

syntax "[mlir_bb|" mlir_bb "]": term

macro_rules 
| `([mlir_bb| ^ $name:ident ( $operands,* ) : $[ $stmts ]* ]) => do
   let initList <- `([])
   let argsList <- operands.getElems.foldlM (init := initList) fun xs x => `($xs ++ [mlir_bb_operand% $x])
   let opsList <- stmts.foldlM (init := initList) fun xs x => `($xs ++ [[mlir_bb_stmt|$x]])
   `(BasicBlock.mk $(Lean.quote (toString name.getId)) $argsList $opsList)
| `([mlir_bb| ^ $name:ident : $[ $stmts ]* ]) => do
   let initList <- `([])
   let opsList <- stmts.foldlM (init := initList) fun xs x => `($xs ++ [[mlir_bb_stmt|$x]])
   `(BasicBlock.mk $(Lean.quote (toString name.getId)) [] $opsList)


-- EDSL MLIR REGIONS
-- =================

syntax "{" (ws mlir_bb ws)* "}": mlir_region
syntax "[mlir_region|" mlir_region "]" : term
syntax "<[" term "]>" : mlir_region
syntax "{{" term "}}" : mlir_region

macro_rules
| `([mlir_region| { $[ $bbs ]* } ]) => do
   let initList <- `([])
   let bbsList <- bbs.foldlM (init := initList) fun xs x => `($xs ++ [[mlir_bb|$x]])
   `(Region.mk $bbsList)

macro_rules
| `([mlir_region| <[ $t: term ]> ]) => t
| `([mlir_region| {{ $t: term }} ]) => t



-- MLIR ATTRIBUTE VALUE
-- ====================

declare_syntax_cat mlir_attr_val

syntax str: mlir_attr_val
syntax mlir_type : mlir_attr_val

syntax "mlir_attr_val%" mlir_attr_val : term

macro_rules 
  | `(mlir_attr_val% $s:strLit) => `(AttrVal.str $s)
  | `(mlir_attr_val% $ty:mlir_type) => `(AttrVal.type [mlir_type| $ty])


def attrVal0Str : AttrVal := mlir_attr_val% "foo"
#print attrVal0Str

def attrVal1Ty : AttrVal := mlir_attr_val% (i32, i64) -> i32
#print attrVal1Ty

-- MLIR ATTRIBUTE
-- ===============

declare_syntax_cat mlir_attr

syntax ident "=" mlir_attr_val : mlir_attr

-- | TODO: change to [mlir_attr| .. ]
syntax "mlir_attr%" mlir_attr : term

macro_rules 
  | `(mlir_attr% $name:ident  = $v:mlir_attr_val) => 
     `(Attr.mk $(Lean.quote (toString name.getId))  (mlir_attr_val% $v))

def attr0Str : Attr := (mlir_attr% sym_name = "add")
#print attr0Str

def attr1Type : Attr := (mlir_attr% type = (i32, i32) -> i32)
#print attr1Type

-- MLIR OPS WITH REGIONS AND ATTRIBUTES AND BASIC BLOCK ARGS
-- =========================================================


syntax strLit "(" mlir_op_operand,* ")" ("[" mlir_op_successor_arg,* "]")? ("(" mlir_region,* ")")?  ("{" mlir_attr,* "}")? ":" mlir_type : mlir_op


macro_rules 
  | `([mlir_op| $name:strLit 
        ( $operands,* )
        $[ [ $succ,* ] ]?
        $[ ( $rgns,* ) ]?
        $[ { $attrs,* } ]? : $ty:mlir_type ]) => do
        let initList <- `([])
        let operandsList <- operands.getElems.foldlM (init := initList) fun xs x => `($xs ++ [[mlir_op_operand| $x]])
        let succList <- match succ with
                | none => `([])
                | some xs => xs.getElems.foldlM (init := initList) fun xs x => `($xs ++ [[mlir_op_successor_arg| $x] ])
        let attrsList <- match attrs with 
                          | none => `([]) 
                          | some attrs => attrs.getElems.foldlM (init := initList) fun xs x => `($xs ++ [mlir_attr% $x])
        let rgnsList <- match rgns with 
                          | none => `([]) 
                          | some rgns => rgns.getElems.foldlM (init := initList) fun xs x => `($xs ++ [[mlir_region| $x]])
        `(Op.mk $name -- name
                $operandsList -- operands
                $succList -- bbs
                $rgnsList -- regions
                $attrsList -- attrs
                [mlir_type| $ty]) -- type


def bbstmt1 : BasicBlockStmt := 
  [mlir_bb_stmt| "foo"(%x, %y) : (i32, i32) -> i32]
#print bbstmt1
def bbstmt2: BasicBlockStmt := 
  [mlir_bb_stmt| %z = "foo"(%x, %y) : (i32, i32) -> i32]
#print bbstmt2

def bbop1 : SSAVal × MLIRTy := mlir_bb_operand% %x : i32
#print bbop1

def bb1NoArgs : BasicBlock := 
  [mlir_bb|
     ^entry:
     "foo"(%x, %y) : (i32, i32) -> i32
      %z = "bar"(%x) : (i32) -> (i32)
      "std.return"(%x0) : (i42) -> ()
  ]
#print bb1NoArgs

def bb2SingleArg : BasicBlock := 
  [mlir_bb|
     ^entry(%argp : i32):
     "foo"(%x, %y) : (i32, i32) -> i32
      %z = "bar"(%x) : (i32) -> (i32)
      "std.return"(%x0) : (i42) -> ()
  ]
#print bb2SingleArg


def bb3MultipleArgs : BasicBlock := 
  [mlir_bb|
     ^entry(%argp : i32, %argq : i64):
     "foo"(%x, %y) : (i32, i32) -> i32
      %z = "bar"(%x) : (i32) -> (i32)
      "std.return"(%x0) : (i42) -> ()
  ]
#print bb3MultipleArgs


def rgn0 : Region := ([mlir_region|  { }])
#print rgn0

def rgn1 : Region := 
  [mlir_region|  { 
    ^entry:
      "std.return"(%x0) : (i42) -> ()
  }]
#print rgn1

def rgn2 : Region := 
  [mlir_region|  { 
    ^entry:
      "std.return"(%x0) : (i42) -> ()

    ^loop:
      "std.return"(%x1) : (i42) -> ()
  }]
#print rgn2


-- | test simple ops [no regions]
def opcall1 : Op := [mlir_op| "foo" (%x, %y) : (i32, i32) -> i32 ]
#print opcall1


def opattr0 : Op := [mlir_op|
 "foo"() { sym_name = "add", type = (i32, i32) -> i32 } : () -> ()
]
#print opattr0


def oprgn0 : Op := [mlir_op|
 "func"() ( {
  ^bb0(%arg0: i32, %arg1: i32):
    %x = "std.addi"(%arg0, %arg1) : (i32, i32) -> i32
    "std.return"(%x) : (i32) -> ()
  }) : () -> ()
]
#print oprgn0


-- | note that this is a "full stack" example!
def opRgnAttr0 : Op := [mlir_op|
 "module"() (
 {
  ^entry:
   "func"() (
    {
     ^bb0(%arg0:i32, %arg1:i32):
      %zero = "std.addi"(%arg0 , %arg1) : (i32, i32) -> i32
      "std.return"(%zero) : (i32) -> ()
    }){sym_name = "add", type = (i32, i32) -> i32} : () -> ()
   "module_terminator"() : () -> ()
 }) : () -> ()
]
#print opRgnAttr0



-- | test simple ops [no regions, but with bb args]
def opcall2 : Op := [mlir_op| "foo" (%x, %y) [^bb1, ^bb2] : (i32, i32) -> i32]
#print opcall2

end MLIR.EDSL
