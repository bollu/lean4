/-
Copyright (c) 2020 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Siddharth Bhat

This file constructs the bounded recursion principles from the raw
primitive recursor.

Recall that the bounded recursion principle, also known
as "course of values recursion",
(https://en.wikipedia.org/wiki/Course-of-values_recursion),
allows a function definition of `f(n)` to refer to the previous
values of function `f(n-1), f(n-2), ..., f(n-k)` for a constant `k`.
-/

/-
Porting functions from:
https://github.com/leanprover/lean4/blob/684f32fabe06a33c77973af7e4f4f9acfa1fc087/src/library/constructions/brec_on.cpp#L361

This connects to lean from:
https://github.com/leanprover/lean4/blob/7c38649527c85116345df831254985afa2680dd0/src/Lean/Meta/Constructions.lean#L11-L31
-/
import Lean.AuxRecursor
import Lean.Meta.AppBuilder
import Lean.Meta.RecursorInfo
import Lean.Meta.Basic
import Lean.Declaration
import Lean.Modifiers
import Lean.Server.Completion

namespace Lean
namespace BrecOn

open Lean Meta

@[extern "lean_mk_cases_on"] opaque mkCasesOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_rec_on"] opaque mkRecOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_no_confusion"] opaque mkNoConfusionCoreImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_below"] opaque mkBelowImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_ibelow"] opaque mkIBelowImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_brec_on"] opaque mkBRecOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment
@[extern "lean_mk_binduction_on"] opaque mkBInductionOnImp (env : Environment) (declName : @& Name) : Except KernelException Environment

abbrev MkBelowM := StateT LocalContext MetaM

def MkBelowM.inferType (e : Expr) : MkBelowM Expr := do
  let lctx : LocalContext ← get
  Meta.withLCtx lctx (← Meta.getLocalInstances) (Meta.inferType e)

variable [Monad m] [MonadEnv m] [MonadError m] [MonadOptions m]

@[inline] private def adaptFn (f : Environment → Name → Except KernelException Environment) (declName : Name) : m Unit := do
  let env ← ofExceptKernelException (f (← getEnv) declName)
  modifyEnv fun _ => env

def mkCasesOn (declName : Name) : m Unit := adaptFn mkCasesOnImp declName
def mkRecOn (declName : Name) : m Unit := adaptFn mkRecOnImp declName
def mkNoConfusionCore (declName : Name) : m Unit := adaptFn mkNoConfusionCoreImp declName

def isRecursiveDatatype (declName : Name) : MetaM Bool := do
  match (← getEnv).find? declName with
  | .some (.inductInfo indval) => pure indval.isRec
  | _ => return False


-- level mk_univ_param(name const & n) { return level(lean_level_mk_param(n.to_obj_arg())); }
def mkUnivParam (n : Name) : Level := mkLevelParam n

-- forallTelescopeReducing, isInductivePredicate
/-- Return `true` if `declName` is an inductive predicate. That is, `inductive` type in `Prop`. -/
/-
def isInductivePredicate (declName : Name) : MetaM Bool := do
  match (← getEnv).find? declName with
  | some (.inductInfo { type := type, ..}) =>
    forallTelescopeReducing type fun _ type => do
      match (← whnfD type) with
      | .sort u .. => return u == levelZero
      | _ => return false
  | _ => return false
-/
/-
level get_datatype_level(environment const & env, expr const & ind_type) {
    local_ctx lctx;
    name_generator ngen(*g_util_fresh);
    expr it = type_checker(env, lctx).whnf(ind_type);
    while (is_pi(it)) {
        expr local = lctx.mk_local_decl(ngen, binding_name(it), binding_domain(it), binding_info(it));
        it = type_checker(env, lctx).whnf(instantiate(binding_body(it), local));
    }
    if (is_sort(it)) {
        return sort_level(it);
    } else {
        throw exception("invalid inductive datatype type");
    }
}
-/

def getDatatypeLevel (env_ : Environment) (type : Expr) : MetaM Level :=
  Meta.forallTelescopeReducing type fun args body =>
    if body.isSort
    then return body.sortLevel!
    else throwError "invalid inductive datatype type"

def isTypeformerApp (typeformerNames : Array Name) (e : Expr) : Option Nat :=  Id.run do
  let fn := e.appFn!
  if !fn.isFVar
  then .none
  else do
    let mut r := 0
    for name in typeformerNames do 
      if fn.fvarId!.name == name 
      then return .some r
      r := r + 1
    return .none


def mkDefinitionInferringUnsafe (name : Name) (levelParams : List Name) (type : Expr) (value : Expr)
  (reducibilityHints : ReducibilityHints) : MetaM Declaration := do 
    let env ← getEnv
    let unsafe_ : DefinitionSafety := 
      if env.hasUnsafe value || env.hasUnsafe type
      then DefinitionSafety.unsafe
      else DefinitionSafety.safe
    return Declaration.defnDecl ({
      name := name
      levelParams := levelParams,
      type := type
      value := value,
      hints := reducibilityHints,
      safety := unsafe_,
      all := [] -- TODO: is this correct?
      : DefinitionVal
    })

  /-
    if (ibelow) {
        // we are eliminating to Prop
        blvls      = tail(lps);
        rlvl       = mk_level_zero();
        ref_type   = instantiate_lparam(rec_info.get_type(), param_id(lvl), mk_level_zero());
    } else if (is_reflexive) {
        blvls = lps;
        rlvl  = get_datatype_level(env, ind_info.get_type());
        // if rlvl is of the form (max 1 l), then rlvl <- l
        if (is_max(rlvl) && is_one(max_lhs(rlvl)))
            rlvl = max_rhs(rlvl);
        rlvl       = mk_max(mk_succ(lvl), rlvl);
        ref_type   = instantiate_lparam(rec_info.get_type(), param_id(lvl), mk_succ(lvl));
    } else {
        // we can simplify the universe levels for non-reflexive datatypes
        blvls       = lps;
        rlvl        = mk_max(mk_level_one(), lvl);
        ref_type    = rec_info.get_type();
    }
-/
def mkRefType (isReflexive : Bool) (indInfo : ConstantInfo) (recInfo : InductiveVal) (lvl : Level) (lps : List Name) (ibelow : Bool) :
    MetaM (List Name × Level × Expr):= do
  if ibelow then
    -- we are eliminating to Prop
    let blvls := lps.tailD []
    let rlvl := Level.zero
    let (Level.param lvlParamId) := lvl
      | throwError "level parameter must be a Level.param"
    let refType := recInfo.type.instantiateLevelParams [lvlParamId] [Level.zero]
    return (blvls, rlvl, refType)
  else if isReflexive
  then
    let rlvl ← getDatatypeLevel (← getEnv) indInfo.type
    -- if rlvl is of the form (max 1 l), then rlvl <- l
    let rlvl := -- TODO: should this be normalized first?
      match rlvl with
      | .max (.succ .zero) rhs => rhs
      | _ => rlvl
    let rlvl := Level.max (Level.succ lvl) rlvl
    -- TODO: is `instantiateTypeLevelParams` the correct function?
    -- TODO: why is the `lvl` always going to be a parameter?
    let (Level.param lvlParamId) := lvl
      | throwError "level parameter must be a Level.param"
    let ref_type := recInfo.type.instantiateLevelParams [lvlParamId] [Level.succ lvl]
    pure (lps, rlvl, ref_type)
  else
      -- we can simplify the universe levels for non-reflexive datatypes
      pure (lps, Level.max levelOne lvl, recInfo.type)


/-
static environment mk_below(environment const & env, name const & n, bool ibelow) {
    if (!is_recursive_datatype(env, n))
        return env;
    if (is_inductive_predicate(env, n))
        return env;
    local_ctx lctx;
    constant_info ind_info = env.get(n);
    inductive_val ind_val  = ind_info.to_inductive_val();
    name_generator ngen    = mk_constructions_name_generator();
    unsigned nparams       = ind_val.get_nparams();
    constant_info rec_info = env.get(mk_rec_name(n));
    recursor_val rec_val   = rec_info.to_recursor_val();
    unsigned nminors       = rec_val.get_nminors();
    unsigned ntypeformers  = rec_val.get_nmotives();
    names lps              = rec_info.get_lparams();
    bool is_reflexive      = ind_val.is_reflexive();
    level  lvl             = mk_univ_param(head(lps));
    levels lvls            = lparams_to_levels(tail(lps));
    names blvls;           // universe parameter names of ibelow/below
    level  rlvl;           // universe level of the resultant type
    // The arguments of below (ibelow) are the ones in the recursor - minor premises.
    // The universe we map to is also different (l+1 for below of reflexive types) and (0 fo ibelow).
    expr ref_type;
    expr Type_result;
    // vvv mkRefType vvvv
    if (ibelow) {
        // we are eliminating to Prop
        blvls      = tail(lps);
        rlvl       = mk_level_zero();
        ref_type   = instantiate_lparam(rec_info.get_type(), param_id(lvl), mk_level_zero());
    } else if (is_reflexive) {
        blvls = lps;
        rlvl  = get_datatype_level(env, ind_info.get_type());
        // if rlvl is of the form (max 1 l), then rlvl <- l
        if (is_max(rlvl) && is_one(max_lhs(rlvl)))
            rlvl = max_rhs(rlvl);
        rlvl       = mk_max(mk_succ(lvl), rlvl);
        ref_type   = instantiate_lparam(rec_info.get_type(), param_id(lvl), mk_succ(lvl));
    } else {
        // we can simplify the universe levels for non-reflexive datatypes
        blvls       = lps;
        rlvl        = mk_max(mk_level_one(), lvl);
        ref_type    = rec_info.get_type();
    }
    Type_result        = mk_sort(rlvl);
    vvv vvvvvvvvvvmkRefArgsvvvvvv
    buffer<expr> ref_args;
    to_telescope(lctx, ngen, ref_type, ref_args);
    lean_assert(ref_args.size() == nparams + ntypeformers + nminors + ind_val.get_nindices() + 1);
    vvvvvvvvvvvvvvvvmkArgs

    // args contains the below/ibelow arguments
    buffer<expr> args;
    buffer<name> typeformer_names;
    // add parameters and typeformers
    vvvvvvvvvvvvvvvv mkArsAndTypeformerNames
    for (unsigned i = 0; i < nparams; i++)
        args.push_back(ref_args[i]);
    for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
        args.push_back(ref_args[i]);
        typeformer_names.push_back(fvar_name(ref_args[i]));
    }
    // we ignore minor premises in below/ibelow
    for (unsigned i = nparams + ntypeformers + nminors; i < ref_args.size(); i++)
        args.push_back(ref_args[i]);
    ^^^^^^^^^^^^^^^^^^^^^^^

    // We define below/ibelow using the recursor for this type
    levels rec_lvls       = cons(mk_succ(rlvl), lvls);
    expr rec              = mk_constant(rec_info.get_name(), rec_lvls);
    vvvvvvvvvvvvvvvv addRecParams vvv
    for (unsigned i = 0; i < nparams; i++)
        rec = mk_app(rec, args[i]);
    vvvvvvvvvvvvvvvvvvvvvvv addRecTypeFormers
    // add type formers
    for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
        buffer<expr> targs;
        to_telescope(lctx, ngen, lctx.get_type(args[i]), targs);
        rec = mk_app(rec, lctx.mk_lambda(targs, Type_result));
    }
    vvvvvvvvvvvvvvvvvvvvvvvvvv addRecMinorPremises
    // add minor premises
    for (unsigned i = nparams + ntypeformers; i < nparams + ntypeformers + nminors; i++) {
        expr minor = ref_args[i];
        expr minor_type = lctx.get_type(minor);
        buffer<expr> minor_args;
        minor_type = to_telescope(lctx, ngen, minor_type, minor_args);
        buffer<expr> prod_pairs;
        vvvvvv addRecMinorPremiseAddMinorArg vvvvvvvvvvvvvv
        for (expr & minor_arg : minor_args) {
            buffer<expr> minor_arg_args;
            expr minor_arg_type = to_telescope(env, lctx, ngen, lctx.get_type(minor_arg), minor_arg_args);
            if (is_typeformer_app(typeformer_names, minor_arg_type)) {
                expr fst  = lctx.get_type(minor_arg);
                minor_arg = lctx.mk_local_decl(ngen, lctx.get_local_decl(minor_arg).get_user_name(), lctx.mk_pi(minor_arg_args, Type_result));
                expr snd  = lctx.mk_pi(minor_arg_args, mk_app(minor_arg, minor_arg_args));
                type_checker tc(env, lctx);
                prod_pairs.push_back(mk_pprod(tc, fst, snd, ibelow));
            }
        }
        vvvvvvvvaddRecMinorPremiseMkNewArg
        type_checker tc(env, lctx);
        expr new_arg = foldr([&](expr const & a, expr const & b) { return mk_pprod(tc, a, b, ibelow); },
                             [&]() { return mk_unit(rlvl, ibelow); },
                             prod_pairs.size(), prod_pairs.data());
        rec = mk_app(rec, lctx.mk_lambda(minor_args, new_arg));
    }
    ^^^^^^^^^^^^^^^^^^^^^^^^^^

    vvvvvvvvvvvvvvvvvvvvvvvvvv addRecIndicesAndMajorPremises
    // add indices and major premise
    for (unsigned i = nparams + ntypeformers; i < args.size(); i++) {
        rec = mk_app(rec, args[i]);
    }

    vvvvvvvvvvvvvvvvvvvvvvvvvv mkBelowAuxAddToEnv
    name below_name  = ibelow ? name{n, "ibelow"} : name{n, "below"};
    expr below_type  = lctx.mk_pi(args, Type_result);
    expr below_value = lctx.mk_lambda(args, rec);

    declaration new_d = mk_definition_inferring_unsafe(env, below_name, blvls, below_type, below_value,
                                                       reducibility_hints::mk_abbreviation());
    environment new_env = env.add(new_d);
    new_env = set_reducible(new_env, below_name, reducible_status::Reducible, true);
    new_env = completion_add_to_black_list(new_env, below_name);
    return add_protected(new_env, below_name);
}
-/

-- for (unsigned i = 0; i < nparams; i++)
--     rec = mk_app(rec, args[i]);
def addRecParams (rec_ : Expr) (args : Array Expr) (nparams : Nat) : MetaM Expr := do
  let mut rec_ := rec_
  for i in [0:nparams] do
    rec_ := Expr.app rec_ args[i]!
  return rec_


def addRecMinorPremiseAddMinorArg (minorArgs : Array Expr) (minorArg : Expr)
    (typeformerNames : Array Name) (prodPairs : Array Expr) :
    MetaM (Expr × Array Expr) := do
  let mut prodPairs := prodPairs
  let (minorArgArgs, minorArgType) ← forallTelescope (← inferType minorArg)
    (fun minorArgArgs minorArgType => return (minorArgArgs, minorArgType))
  let mut minorArg := minorArg
  if (isTypeformerApp typeformerNames minorArgType).isSome then
    let fst ← inferType minorArg
    -- | TODO: still not sure how to create a new local decl.
    -- `withLocalDecl` expects a continuation, which makes the rest of the code
    --   also need to be CPSd. This seems super painful, especially because
    --   the call site of this function performs a loop, which is even more annoying to CPS!
    -- minorArg := (← getLCtx).mkLocalDecl
    --                   (fvarId := sorry) -- TODO: what's the correct fvarId?
    --                   (userName := ((← getLCtx).get! minorArg.fvarId!).userName)
    --                   (type := (← getLCtx).mkForall minorArgArgs typeResult)
    let snd := (← getLCtx).mkForall minorArgs (← mkAppM' minorArg minorArgArgs)
    let pair := (← Lean.Meta.mkAppM ``PProd.mk #[fst, snd])
    prodPairs := prodPairs.push pair
  return (minorArg, prodPairs)

def addRecMinorPremises (rec_ : Expr) (refArgs : Array Expr) (typeformerNames : Array Name)
    (nparams ntypeformers nminors : Nat) : MetaM Expr := do
  let mut rec_ := rec_
  for i in [nparams+ntypeformers:nparams+ntypeformers+nminors] do
    let minor := refArgs[i]!
    let minorType := ((← getLCtx).get! minor.fvarId!).type
    let (minorArgs_, minorType) ← Meta.forallTelescope minorType (fun minorArgs minorType => return (minorArgs, minorType))
    let mut minorArgs := minorArgs_
    let mut prodPairs : Array Expr := #[]
    for i in [0:minorArgs.size] do
      let minorArg := minorArgs[i]!
      let (minorArg, prodPairs_) ← addRecMinorPremiseAddMinorArg minorArgs minorArg typeformerNames prodPairs
      prodPairs := prodPairs_
      minorArgs := minorArgs.set! i minorArg

    let newArg ← prodPairs.foldrM
      (init := ← Lean.Meta.mkAppM ``Unit.unit #[])
      (f := fun a b => Lean.Meta.mkAppM ``PProd.mk #[a, b])
    rec_ :=  Expr.app rec_ ((← getLCtx).mkLambda minorArgs newArg)
  return rec_


/-
for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
    buffer<expr> targs;
    to_telescope(lctx, ngen, lctx.get_type(args[i]), targs);
    rec = mk_app(rec, lctx.mk_lambda(targs, Type_result));
}
-/
def addRecTypeformers (rec_ : Expr) (args : Array Expr) (typeResult : Expr) (nparams ntypeformers : Nat) : MetaM Expr := do
  let mut rec_ := rec_
  for i in [nparams:nparams+ntypeformers] do
    let targs ← Meta.forallTelescope (← inferType args[i]!) (fun targs _ => return targs)
    rec_ ← mkLambdaFVars targs typeResult
  return rec_

/-

Uses ot `to_telescope`:

#### 81:to_telescope(lctx, ngen, ref_type, ref_args)
- used line 111:expr minor = ref_args[i].

#### 106:to_telescope(lctx, ngen, lctx.get_type(args[i]), targs)
- 107:rec = mk_app(rec, lctx.mk_lambda(targs, Type_result));`
- Live range ends immediately.

#### 114:to_telescope(lctx, ngen, minor_type, minor_args);
- Live range ends after a loop.
- 131:rec = mk_app(rec, lctx.mk_lambda(minor_args, new_arg));


#### 118:minor_arg_type = to_telescope(env, lctx, ngen, lctx.get_type(minor_arg), minor_arg_args);
- Live range ends 4 lines after straight line code.
- 119:if (is_typeformer_app(typeformer_names, minor_arg_type)) ...
- 121:minor_arg = lctx.mk_local_decl(ngen, lctx.get_local_decl(minor_arg).get_user_name(), lctx.mk_pi(minor_arg_args, Type_result));
- 122:expr snd = lctx.mk_pi(minor_arg_args, mk_app(minor_arg, minor_arg_args));

-/

-- Since `forallTelescoping`'s API is continuation based, I am entirely unsure
--   if this way of encoding the above `for` loop is correct.
-- TODO: totally unsure if `inferType` is the correct way to grab the type.
-- for (unsigned i = 0; i < nparams; i++)
--     args.push_back(ref_args[i]);
-- for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
--     args.push_back(ref_args[i]);
--     typeformer_names.push_back(fvar_name(ref_args[i]));
-- }
-- for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
--     buffer<expr> targs;
--     to_telescope(lctx, ngen, lctx.get_type(args[i]), targs);
--     rec = mk_app(rec, lctx.mk_lambda(targs, Type_result));
-- }
def mkArgsAndTypeformerNames (refArgs : Array Expr) (nparams ntypeformers nminors : Nat) : MetaM (Array Expr × Array Name) := do
    let mut args : Array Expr := refArgs.shrink nparams
    let mut typeformerNames := #[]
    for i in [nparams:nparams+ntypeformers] do
      args := args.push <| refArgs[i]!
      typeformerNames := typeformerNames.push <| refArgs[i]! |>.fvarId! |>.name
    for i in [nparams+ntypeformers:nparams+ntypeformers+nminors] do
      args := args.push <| refArgs[i]!
    return (args, typeformerNames)

def mkBelow' (declName : Name) (ibelow : Bool) : MetaM Unit := do
  if ! (← isRecursiveDatatype declName) then return ()
  if (← isInductivePredicate declName) then return ()
  let .some indInfo := (← getEnv).find? declName | return ()
  let .inductInfo indVal := indInfo | return ()
  let nparams := indVal.numParams
  let recVal : RecursorVal ← getConstInfoRec (mkRecName declName)
  let nminors := recVal.numMinors
  let ntypeformers := recVal.numMotives
  let recInfo ← getConstInfoInduct recVal.getInduct
  let lps := recInfo.levelParams
  let isReflexive := indVal.isReflexive
  let lvl := mkUnivParam lps[0]!

  let lvls := lps |>.drop 1 |>.map mkLevelParam
  adaptFn mkBelowImp declName

  let (blvls, rlvl, ref_type) ← mkRefType isReflexive indInfo recInfo lvl lps ibelow
  let typeResult := Expr.sort rlvl
  let refArgs ← Meta.forallTelescope ref_type (fun refArgs _ => return refArgs)
  let (args, typeformerNames) ← mkArgsAndTypeformerNames refArgs nparams ntypeformers nminors
  let recLvls : List Level := (Level.succ rlvl)::lvls
  let mut rec_ : Expr := Expr.const recInfo.name recLvls
  rec_ ← addRecParams rec_ args nparams
  rec_ ← addRecTypeformers rec_ args typeResult nparams ntypeformers
  rec_ ← addRecMinorPremises rec_ refArgs typeformerNames nparams ntypeformers nminors
  let belowName : Name :=
    if ibelow
    then (Name.str declName "ibelow")
    else (Name.str declName "below")
  let belowType ←  mkForallFVars args typeResult -- TODO: is this the correct function?
  let belowValue ← mkLambdaFVars args rec_ -- TODO: is this the correct function?
  let newD : Declaration ←
    mkDefinitionInferringUnsafe belowName blvls belowType belowValue
      ReducibilityHints.abbrev
  modifyEnv fun env =>
    match env.addDecl newD with
    | Except.ok newEnv => newEnv
    | Except.error err => env -- TODO: what to do if we get an error?
  setReducibilityStatus belowName ReducibilityStatus.reducible
  modifyEnv <| Server.Completion.addToBlackList (declName := belowName)
  modifyEnv <| addProtected (n := belowName)

def mkIBelow (declName : Name) : m Unit := adaptFn mkIBelowImp declName
def mkBRecOn (declName : Name) : m Unit := adaptFn mkBRecOnImp declName
def mkBInductionOn (declName : Name) : m Unit := adaptFn mkBInductionOnImp declName
end BrecOn

end Lean
