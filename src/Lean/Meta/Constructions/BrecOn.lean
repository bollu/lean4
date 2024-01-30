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

def getDatatypeLevel (env : Environment) (type : Expr) : Level := sorry

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

def mkBelow (declName : Name) : MetaM Unit := do
  if ! (← isRecursiveDatatype declName) then return ()
  if (← isInductivePredicate declName) then return ()
  -- local_ctx lctx;
  -- constant_info ind_info = env.get(n);
  let .some indInfo := (← getEnv).find? declName | return ()
  -- inductive_val ind_val  = ind_info.to_inductive_val();
  let .inductInfo indVal := indInfo | return ()
  -- name_generator ngen    = mk_constructions_name_generator();
  -- unsigned nparams       = ind_val.get_nparams();
  let nparams := indVal.numParams
  -- constant_info rec_info = env.get(mk_rec_name(n));
  -- recursor_val rec_val   = rec_info.to_recursor_val();
  let recVal : RecursorVal ← getConstInfoRec (mkRecName declName)
  -- unsigned nminors       = rec_val.get_nminors();
  let nminors := recVal.numMinors
  -- unsigned ntypeformers  = rec_val.get_nmotives();
  let ntypeformers := recVal.numMotives
  let recInfo ← getConstInfoInduct recVal.getInduct
  -- names lps              = rec_info.get_lparams();
  let lps := recInfo.levelParams
  -- bool is_reflexive      = ind_val.is_reflexive();
  let isReflexive := indVal.isReflexive
  -- level  lvl             = mk_univ_param(head(lps));
  let lvl := mkUnivParam lps[0]!
  -- levels lvls            = lparams_to_levels(tail(lps));
  let lvls := lps |>.drop 1 |>.map mkLevelParam
  -- names blvls;           // universe parameter names of ibelow/below
  -- level  rlvl;           // universe level of the resultant type
  adaptFn mkBelowImp declName

--   -- // The arguments of below (ibelow) are the ones in the recursor - minor premises.
--   -- // The universe we map to is also different (l+1 for below of reflexive types) and (0 fo ibelow).
--   -- expr ref_type;
--   -- expr Type_result;
--     -- if (ibelow) {
--     --     // we are eliminating to Prop
--     --     blvls      = tail(lps);
--     --     rlvl       = mk_level_zero();
--     --     ref_type   = instantiate_lparam(rec_info.get_type(), param_id(lvl), mk_level_zero());
--     -- } else if (is_reflexive) {
--     --     blvls = lps;
--     --     rlvl  = get_datatype_level(env, ind_info.get_type());
--     --     // if rlvl is of the form (max 1 l), then rlvl <- l
--     --     if (is_max(rlvl) && is_one(max_lhs(rlvl)))
--     --         rlvl = max_rhs(rlvl);
--     --     rlvl       = mk_max(mk_succ(lvl), rlvl);
--     --     ref_type   = instantiate_lparam(rec_info.get_type(), param_id(lvl), mk_succ(lvl));
--     -- } else {
--     --     // we can simplify the universe levels for non-reflexive datatypes
--     --     blvls       = lps;
--     --     rlvl        = mk_max(mk_level_one(), lvl);
--     --     ref_type    = rec_info.get_type();
--     -- }

  let (blvls, rlvl, ref_type) ← do -- : List Name × Level × Expr := ← do
    if isReflexive
    then 
      let rlvl := getDatatypeLevel (← getEnv) indInfo.type
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
        pure (lps, Level.max levelOne lvl, recInfo.type)
--     -- Type_result        = mk_sort(rlvl);
  let typeResult := Expr.sort rlvl
--     -- buffer<expr> ref_args;
--     -- to_telescope(lctx, ngen, ref_type, ref_args);
  forallTelescope ref_type fun refArgs _refBody => do 
--     -- lean_assert(ref_args.size() == nparams + ntypeformers + nminors + ind_val.get_nindices() + 1);
-- 
--     -- // args contains the below/ibelow arguments
--     -- buffer<expr> args;
--     -- buffer<name> typeformer_names;
--     -- // add parameters and typeformers
--     -- for (unsigned i = 0; i < nparams; i++)
--     --     args.push_back(ref_args[i]);
    let mut args : Array Expr := #[]
--     -- for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
--     --     args.push_back(ref_args[i]);
--     --     typeformer_names.push_back(fvar_name(ref_args[i]));
--     -- }
    -- TODO: range has no map
    let mut typeformerNames := #[]
    for i in [nparams:nparams+ntypeformers] do
      args := args.push <| refArgs[i]!
      typeformerNames := typeformerNames.push <| refArgs[i]! |>.fvarId! |>.name 
--     -- // we ignore minor premises in below/ibelow
--     -- for (unsigned i = nparams + ntypeformers + nminors; i < ref_args.size(); i++)
--     --     args.push_back(ref_args[i]);
-- 
--     -- // We define below/ibelow using the recursor for this type
--     -- levels rec_lvls       = cons(mk_succ(rlvl), lvls);
    let recLvls : List Level := (Level.succ rlvl)::lvls
--     -- expr rec              = mk_constant(rec_info.get_name(), rec_lvls);
    let mut rec_ : Expr := Expr.const recInfo.name recLvls
--     -- for (unsigned i = 0; i < nparams; i++)
--     --     rec = mk_app(rec, args[i]);
    rec_ := args.foldl (init := rec_) (fun accum arg => Expr.app accum arg)
--     -- // add type formers
--     -- for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
--     --     buffer<expr> targs;
--     --     to_telescope(lctx, ngen, lctx.get_type(args[i]), targs);
--     --     rec = mk_app(rec, lctx.mk_lambda(targs, Type_result));
--     -- }
    for i in [nparams:nparams+ntypeformers] do 
      -- TODO: what is the correct way to convert this piece of code?
      -- Since `forallTelescoping`'s API is continuation based, I am entirely unsure
      --   if this way of encoding the above `for` loop is correct.
      -- TODO: totally unsure if `inferType` is the correct way to grab the type.
      rec_ ← forallTelescope (← inferType args[i]!) (fun targs _tbody => do
        let lam ← mkLambdaFVars targs typeResult
        pure <| Expr.app rec_ lam)
--     -- // add minor premises
--     -- for (unsigned i = nparams + ntypeformers; i < nparams + ntypeformers + nminors; i++) {
      for i in [nparams+ntypeformers:nparams+ntypeformers+nminors] do 
--       --     expr minor = ref_args[i];
        let minor := refArgs[i]!
--      --     expr minor_type = lctx.get_type(minor);
        -- | TODO: check if this is the correct way to get the type.
        let minorType := ((← getLCtx).get! minor.fvarId!).type
--      --     buffer<expr> minor_args;
        rec_ ←  Meta.forallTelescope minorType (fun minorArgs minorType => do
--      --     minor_type = to_telescope(lctx, ngen, minor_type, minor_args);
--      --     buffer<expr> prod_pairs;
          let mut prodPairs : Array Expr := #[]
          for minorArg in minorArgs do
--      --     for (expr & minor_arg : minor_args) {
--      --         buffer<expr> minor_arg_args;
--      --         expr minor_arg_type = to_telescope(env, lctx, ngen, lctx.get_type(minor_arg), minor_arg_args);
                
--      --         if (is_typeformer_app(typeformer_names, minor_arg_type)) { -- TODO: what is 'is_typeformer_app equialent?
--      --             expr fst  = lctx.get_type(minor_arg);
--      --             minor_arg = lctx.mk_local_decl(ngen,
--      --                lctx.get_local_decl(minor_arg).get_user_name(), lctx.mk_pi(minor_arg_args, Type_result));
--      --             expr snd  = lctx.mk_pi(minor_arg_args, mk_app(minor_arg, minor_arg_args));
--      --             type_checker tc(env, lctx);
--      --             prod_pairs.push_back(mk_pprod(tc, fst, snd, ibelow));
--      --         }
--      --     }
            let pair? ← Meta.forallTelescope (← inferType minorArg) (fun minorArgArgs minorArgType => do
              if (isTypeformerApp typeformerNames minorArgType).isSome then 
                let fst ← inferType minorArg
                --                TODO: does this ACTUALLY mutate the array as it goes along? If so, this should be refactored into a new fn.
                -- | TODO: how to edit the local decl? I need a function with signature `MetaM Unit`.
                let minorArg := (← getLCtx).mkLocalDecl
                                  (fvarId := sorry) -- TODO: what's the correct fvarId?
                                  (userName := ((← getLCtx).get! minorArg.fvarId!).userName)
                                  (type := (← getLCtx).mkForall minorArgArgs typeResult)
                -- TODO: the `sorry` should be minorArg, but I don't know how to add stuff into the local context.
                let snd := (← getLCtx).mkForall minorArgs (← mkAppM' sorry minorArgArgs)
                pure <| Option.some (← Lean.Meta.mkAppM ``PProd.mk #[fst, snd])
              else pure Option.none)
            prodPairs := 
              match pair? with 
              | Option.some pair => prodPairs.push pair
              | Option.none => prodPairs
--      --     type_checker tc(env, lctx);
--      --     expr new_arg = foldr([&](expr const & a, expr const & b) { return mk_pprod(tc, a, b, ibelow); },
--      --                          [&]() { return mk_unit(rlvl, ibelow); },
--      --                          prod_pairs.size(), prod_pairs.data());
            let newArg ← prodPairs.foldrM (init := ← Lean.Meta.mkAppM ``Unit.unit #[])
                                          (f := fun a b => Lean.Meta.mkAppM ``PProd.mk #[a, b])
--      --     rec = mk_app(rec, lctx.mk_lambda(minor_args, new_arg));
            let rec_ := mkApp rec_ (← mkLambdaFVars minorArgs newArg)
--      -- }
          pure rec_)
--    -- // add indices and major premise
--    -- for (unsigned i = nparams + ntypeformers; i < args.size(); i++) {
      for i in [nparams+ntypeformers:args.size] do 
--    --     rec = mk_app(rec, args[i]);
        rec_ :=  Expr.app rec_ args[i]!
--    -- }
-- 
--    -- name below_name  = ibelow ? name{n, "ibelow"} : name{n, "below"};
      let belowName : Name := 
        if false
        then (Name.str declName "ibelow")
        else (Name.str declName "below")
--    -- expr below_type  = lctx.mk_pi(args, Type_result);
      let belowType ←  mkForallFVars args typeResult -- TODO: is this the correct function?
--    -- expr below_value = lctx.mk_lambda(args, rec);
      let belowValue ← mkLambdaFVars args rec_ -- TODO: is this the correct function?
--    -- declaration new_d = mk_definition_inferring_unsafe(env, below_name, blvls, below_type, below_value,
--    --                                                    reducibility_hints::mk_abbreviation());
      let newD : Declaration ← 
        mkDefinitionInferringUnsafe belowName blvls belowType belowValue 
          ReducibilityHints.abbrev
--    -- environment new_env = env.add(new_d);
      modifyEnv fun env => 
        match env.addDecl newD with
        | Except.ok newEnv => newEnv
        | Except.error err => env -- TODO: what to do if we get an error?
--    -- new_env = set_reducible(new_env, below_name, reducible_status::Reducible, true);
      setReducibilityStatus belowName ReducibilityStatus.reducible
--    -- new_env = completion_add_to_black_list(new_env, below_name);
      modifyEnv <| Server.Completion.addToBlackList (declName := belowName)
--    -- return add_protected(new_env, below_name);
      modifyEnv <| addProtected (n := belowName)


def mkIBelow (declName : Name) : m Unit := adaptFn mkIBelowImp declName
def mkBRecOn (declName : Name) : m Unit := adaptFn mkBRecOnImp declName
def mkBInductionOn (declName : Name) : m Unit := adaptFn mkBInductionOnImp declName
end BrecOn

end Lean
