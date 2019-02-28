/-
Copyright (c) 2019 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

A meta def called `#depends` which gives the names of all the theorems (the statement of) a given definition/theorem depends on.
-/

import data.pfun

open tactic expr interactive nat native name list lean.parser environment

/--Takes an expr and spits out a list of all the names in that expr -/
meta def list_names (e : expr): list name :=
e.fold [] (λ e _ es, if is_constant e then insert e.const_name es else es)

/-- Takes an environment and naively lists all declarations in it.-/
meta def list_all_decls (env : environment) : list name :=
env.fold [] $ (λ d ns, d.to_name :: ns)

/-- Takes an environment and lists all declarations in it, much faster. -/
meta def list_all_decls' (env : environment) : rb_set name :=
env.fold (mk_rb_set) $ (λ d ns, ns.insert d.to_name)

/-- Traces all declarations with prefix `namesp` in the current environment. -/
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
    tactic.trace $ list_names d.type

/-- Return the direct dependencies of the *type* of a declaration. -/
meta def name_dir_deps (n : name) : tactic(list name) :=
do env ← get_env,
    l ← get_decl n,
    if is_structure env n then
    do fields ← returnopt $ structure_fields env n,
        let res := map (λ h, name.append n h) fields,
        k ← mmap (λ h, do l ← get_decl h, pure $ list_names l.type) res,
        let clean := list.erase_dup (list.join k),
        let final := list.filter (λ h, ¬ name.is_prefix_of n h) clean,
        pure $ final
    else
    pure $ list_names l.type

/-- Return the direct dependencies of the *value* of a declaration.-/
meta def name_dir_deps_val (n : name) : tactic(list name) :=
do env ← get_env,
    l ← get_decl n,
    if is_structure env n then
    do fields ← returnopt $ structure_fields env n,
        let res := map (λ h, name.append n h) fields,
        k ← mmap (λ h, do l ← get_decl h, pure $ list_names l.value) res,
        let clean := list.erase_dup (list.join k),
        let final := list.filter (λ h, ¬ name.is_prefix_of n h) clean,
        pure $ final
    else
    pure $ list_names l.value


/-- Recursively return a joint list of the m-th sub-dependencies of the type of given name.-/
meta def name_dir_deps_depth (n : name) : ℕ → tactic(list name)
| 0 := name_dir_deps n
| (succ m) :=
 do l ← name_dir_deps_depth m <|> name_dir_deps n,
    l' ← mmap (λ h, name_dir_deps h) l,
    let k := list.erase_dup $
    list.join (l :: l'),
    -- tactic.trace k.length,
    pure $ k

/-- Recursively return a joint list of the m-th sub-dependencies of the type of given name.-/
meta def name_dir_deps_depth_val (n : name) : ℕ → tactic(list name)
| 0 := name_dir_deps_val n
| (succ m) :=
 do l ← name_dir_deps_depth_val m <|> name_dir_deps_val n,
    l' ← mmap (λ h, name_dir_deps h) l,
    let k := list.erase_dup $
    list.join (l :: l'),
    -- tactic.trace k.length,
    pure $ k

theorem foo' : 2+2 = 4 :=
begin
  simp,
end


/- Tests -/
-- #depends nat.has_one
-- #depends group.equiv
-- #depends J4
-- #depends nat.add._main
-- #depends mclaughlin.McL
-- #depends sends_identity_to_1

-- set_option profiler true
-- run_cmd (name_dir_deps_depth_val `mathieu_group.Aut 10) >>= tactic.trace
