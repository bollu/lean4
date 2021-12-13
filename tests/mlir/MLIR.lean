import Lean.Compiler.IR.MLIR

open Lean PrettyPrinter
open MLIR.AST
open MLIR.EDSL

-- EDSL OPERANDS
-- ==============

def xx := ([mlir_op_operand| %x])
def xxx := ([mlir_op_operand| %x])
#print xx
#print xxx


-- EDSL OP-SUCCESSOR-ARGS
-- =================

def succ0 :  BBName := ([mlir_op_successor_arg| ^bb])
#print succ0


-- EDSL MLIR TYPES
-- ===============

def ty0 : MLIRTy := [mlir_type| ()]
def tyi32 : MLIRTy := [mlir_type| i32]
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


-- EDSL MLIR OP CALL, MLIR BB STMT
-- ===============================


-- EDSL MLIR BASIC BLOCK OPERANDS
-- ==============================


-- EDSL MLIR BASIC BLOCKS
-- ======================


-- EDSL MLIR REGIONS
-- =================


-- MLIR ATTRIBUTE VALUE
-- ====================

def attrVal0Str : AttrVal := mlir_attr_val% "foo"
#print attrVal0Str

def attrVal1Ty : AttrVal := mlir_attr_val% (i32, i64) -> i32
#print attrVal1Ty

-- MLIR ATTRIBUTE
-- ===============

def attr0Str : Attr := (mlir_attr% sym_name = "add")
#print attr0Str

def attr1Type : Attr := (mlir_attr% type = (i32, i32) -> i32)
#print attr1Type


-- MLIR OPS WITH REGIONS AND ATTRIBUTES AND BASIC BLOCK ARGS
-- =========================================================

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


----- dummy test main
def main : IO Unit := return ()

