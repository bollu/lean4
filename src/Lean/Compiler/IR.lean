/-
Copyright (c) 2019 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Lean.Compiler.IR.Basic
import Lean.Compiler.IR.Format
import Lean.Compiler.IR.CompilerM
import Lean.Compiler.IR.PushProj
import Lean.Compiler.IR.ElimDeadVars
import Lean.Compiler.IR.SimpCase
import Lean.Compiler.IR.ResetReuse
import Lean.Compiler.IR.NormIds
import Lean.Compiler.IR.Checker
import Lean.Compiler.IR.Borrow
import Lean.Compiler.IR.Boxing
import Lean.Compiler.IR.RC
import Lean.Compiler.IR.ExpandResetReuse
import Lean.Compiler.IR.UnboxResult
import Lean.Compiler.IR.ElimDeadBranches
import Lean.Compiler.IR.EmitC
import Lean.Compiler.IR.EmitMLIR
import Lean.Compiler.IR.CtorLayout
import Lean.Compiler.IR.Sorry

namespace Lean.IR

private def compileAux (decls : Array Decl) : CompilerM Unit := do
  -- log (LogEntry.message "// compileAux")
  -- logDecls `init decls
  -- logPreamble (LogEntry.message mlirPreamble)
  -- logDeclsUnconditional decls
  checkDecls decls
  let decls ← elimDeadBranches decls
  logDecls `elim_dead_branches decls
  let decls := decls.map Decl.pushProj
  logDecls `push_proj decls
  let decls := decls.map Decl.insertResetReuse
  logDecls `reset_reuse decls
  let decls := decls.map Decl.elimDead
  logDecls `elim_dead decls
  -- let decls := decls.map Decl.simpCase
  let decls := decls.map Decl.simpCaseOnlyCanonicalize
  logDecls `simp_case decls
  let decls := decls.map Decl.normalizeIds
  -- logDeclsUnconditional decls

  let decls ← inferBorrow decls
  logDecls `borrow decls
  let decls ← explicitBoxing decls
  logDecls `boxing decls
  let decls ← explicitRC decls
  logDecls `rc decls
  let decls := decls.map Decl.expandResetReuse
  logDecls `expand_reset_reuse decls
  -- | this pass seems to also insert reset/reuse somehow?
  -- let decls := decls.map Decl.pushProj
  logDecls `push_proj decls
  let decls ← updateSorryDep decls
  logDecls `result decls
  checkDecls decls
  addDecls decls


@[export lean_ir_compile]
def compile (env : Environment) (opts : Options) (decls : Array Decl) : Log × (Except String Environment) :=
  match (compileAux decls opts).run { env := env } with
  | EStateM.Result.ok     _  s => (s.log, Except.ok s.env)
  | EStateM.Result.error msg s => (s.log, Except.error msg)

def addBoxedVersionAux (decl : Decl) : CompilerM Unit := do
  let env ← getEnv
  if !ExplicitBoxing.requiresBoxedVersion env decl then
    pure ()
  else
    let decl := ExplicitBoxing.mkBoxedVersion decl
    let decls : Array Decl := #[decl]
    let decls ← explicitRC decls
    decls.forM fun decl => modifyEnv $ fun env => addDeclAux env decl
    pure ()

-- Remark: we are ignoring the `Log` here. This should be fine.
@[export lean_ir_add_boxed_version]
def addBoxedVersion (env : Environment) (decl : Decl) : Except String Environment :=
  match (addBoxedVersionAux decl Options.empty).run { env := env } with
  | EStateM.Result.ok     _  s => Except.ok s.env
  | EStateM.Result.error msg s => Except.error msg

end Lean.IR
