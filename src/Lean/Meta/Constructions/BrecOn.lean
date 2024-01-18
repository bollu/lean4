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

def mkBelow (declName : Name) : MetaM Unit := adaptFn mkBelowImp declName

-- def mkBelow (declName : Name) : m Unit := do
--   -- if (!is_recursive_datatype(env, n)) return env;
--   let recursorInfo ← Lean.Meta.mkRecursorInfo declName
--   if !is_recursive_datatype (declName)
--   then return ()
--   -- if (is_inductive_predicate(env, n)) return env;
--   if !is_inductive_predicate declName
--   then return ()
--   -- local_ctx lctx;
--   -- constant_info ind_info = env.get(n);
--   -- inductive_val ind_val  = ind_info.to_inductive_val();
--   -- name_generator ngen    = mk_constructions_name_generator();
--   -- unsigned nparams       = ind_val.get_nparams();
--   -- constant_info rec_info = env.get(mk_rec_name(n));
--   -- recursor_val rec_val   = rec_info.to_recursor_val();
--   -- unsigned nminors       = rec_val.get_nminors();
--   -- unsigned ntypeformers  = rec_val.get_nmotives();
--   -- names lps              = rec_info.get_lparams();
--   -- bool is_reflexive      = ind_val.is_reflexive();
--   -- level  lvl             = mk_univ_param(head(lps));
--   -- levels lvls            = lparams_to_levels(tail(lps));
--   -- names blvls;           // universe parameter names of ibelow/below
--   -- level  rlvl;           // universe level of the resultant type
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
--     -- Type_result        = mk_sort(rlvl);
--     -- buffer<expr> ref_args;
--     -- to_telescope(lctx, ngen, ref_type, ref_args);
--     -- lean_assert(ref_args.size() == nparams + ntypeformers + nminors + ind_val.get_nindices() + 1);
-- 
--     -- // args contains the below/ibelow arguments
--     -- buffer<expr> args;
--     -- buffer<name> typeformer_names;
--     -- // add parameters and typeformers
--     -- for (unsigned i = 0; i < nparams; i++)
--     --     args.push_back(ref_args[i]);
--     -- for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
--     --     args.push_back(ref_args[i]);
--     --     typeformer_names.push_back(fvar_name(ref_args[i]));
--     -- }
--     -- // we ignore minor premises in below/ibelow
--     -- for (unsigned i = nparams + ntypeformers + nminors; i < ref_args.size(); i++)
--     --     args.push_back(ref_args[i]);
-- 
--     -- // We define below/ibelow using the recursor for this type
--     -- levels rec_lvls       = cons(mk_succ(rlvl), lvls);
--     -- expr rec              = mk_constant(rec_info.get_name(), rec_lvls);
--     -- for (unsigned i = 0; i < nparams; i++)
--     --     rec = mk_app(rec, args[i]);
--     -- // add type formers
--     -- for (unsigned i = nparams; i < nparams + ntypeformers; i++) {
--     --     buffer<expr> targs;
--     --     to_telescope(lctx, ngen, lctx.get_type(args[i]), targs);
--     --     rec = mk_app(rec, lctx.mk_lambda(targs, Type_result));
--     -- }
--     -- // add minor premises
--     -- for (unsigned i = nparams + ntypeformers; i < nparams + ntypeformers + nminors; i++) {
--     --     expr minor = ref_args[i];
--     --     expr minor_type = lctx.get_type(minor);
--     --     buffer<expr> minor_args;
--     --     minor_type = to_telescope(lctx, ngen, minor_type, minor_args);
--     --     buffer<expr> prod_pairs;
--     --     for (expr & minor_arg : minor_args) {
--     --         buffer<expr> minor_arg_args;
--     --         expr minor_arg_type = to_telescope(env, lctx, ngen, lctx.get_type(minor_arg), minor_arg_args);
--     --         if (is_typeformer_app(typeformer_names, minor_arg_type)) {
--     --             expr fst  = lctx.get_type(minor_arg);
--     --             minor_arg = lctx.mk_local_decl(ngen,
--     --                lctx.get_local_decl(minor_arg).get_user_name(), lctx.mk_pi(minor_arg_args, Type_result));
--     --             expr snd  = lctx.mk_pi(minor_arg_args, mk_app(minor_arg, minor_arg_args));
--     --             type_checker tc(env, lctx);
--     --             prod_pairs.push_back(mk_pprod(tc, fst, snd, ibelow));
--     --         }
--     --     }
--     --     type_checker tc(env, lctx);
--     --     expr new_arg = foldr([&](expr const & a, expr const & b) { return mk_pprod(tc, a, b, ibelow); },
--     --                          [&]() { return mk_unit(rlvl, ibelow); },
--     --                          prod_pairs.size(), prod_pairs.data());
--     --     rec = mk_app(rec, lctx.mk_lambda(minor_args, new_arg));
--     -- }
-- 
--     -- // add indices and major premise
--     -- for (unsigned i = nparams + ntypeformers; i < args.size(); i++) {
--     --     rec = mk_app(rec, args[i]);
--     -- }
-- 
--     -- name below_name  = ibelow ? name{n, "ibelow"} : name{n, "below"};
--     -- expr below_type  = lctx.mk_pi(args, Type_result);
--     -- expr below_value = lctx.mk_lambda(args, rec);
-- 
--     -- declaration new_d = mk_definition_inferring_unsafe(env, below_name, blvls, below_type, below_value,
--     --                                                    reducibility_hints::mk_abbreviation());
--     -- environment new_env = env.add(new_d);
--     -- new_env = set_reducible(new_env, below_name, reducible_status::Reducible, true);
--     -- new_env = completion_add_to_black_list(new_env, below_name);
--     -- return add_protected(new_env, below_name);


def mkIBelow (declName : Name) : m Unit := adaptFn mkIBelowImp declName
def mkBRecOn (declName : Name) : m Unit := adaptFn mkBRecOnImp declName
def mkBInductionOn (declName : Name) : m Unit := adaptFn mkBInductionOnImp declName
end BrecOn

end Lean
