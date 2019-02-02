/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

A meta def called `#depends` which gives the names of all the theorems (the statement of) a given definition/theorem depends on.
-/

import data.buffer.parser
import tactic.squeeze

open tactic expr interactive native name list lean.parser parser

universe u

variables {s : Type u} 

/-Takes an expr and spits out a list of all the names in that expr -/
meta def list_names (e : expr): list name :=
e.fold [] (λ e _ es, if is_constant e then insert e.const_name es else es)

/- Takes an environment and naively lists all declarations in it.-/
meta def list_all_decls (env : environment) : list name :=
env.fold [] $ (λ d ns, d.to_name :: ns)

/- Takes an environment and lists all declarations in it, much faster. -/
meta def list_all_decls' (env : environment) : rb_set name :=
env.fold (mk_rb_set) $ (λ d ns, ns.insert d.to_name)

/- Traces all declarations with prefix namesp in the current environment. -/
/-TODO : optimize using rb_set filters and maps(?)-/
meta def trace_all_decls (namesp : name) : tactic unit :=
do e ← get_env,
   let l := list_all_decls' e,
   let k := l.to_list,
   let m := list.map (λ h:name, h.get_prefix) k,
   let f := k.filter (λ h, is_prefix_of namesp h),
   tactic.trace $ take 150 f,
   skip

/- TODO : modify this to take structures into account -/
@[user_command] meta def depends_cmd (meta_info : decl_meta_info) ( _ : parse $ tk "#depends")
 : lean.parser unit
:= do given_name ← ident,
    resolved ← resolve_constant given_name,
    d ← get_decl resolved <|> fail ("declaration " ++ to_string given_name ++ " not found"),
    tactic.trace $ d.type 

meta def direct_dependencies : tactic unit :=
do  t ← tactic.target,
    let k := list_names t,
    -- pure $ to_string k
    tactic.trace k

theorem foo : 2+2 = 4 :=
begin
-- direct_dependencies,
-- trace_all_decls `name,
squeeze_simp,
end
#check eq_self_iff_true
#depends foo 
-- #depends cond_prob_swap
-- #depends total_prob
-- #depends group.equiv
-- #depends isomorphic
-- #depends is_simple_alternating_group