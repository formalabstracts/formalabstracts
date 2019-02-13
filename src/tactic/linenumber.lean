/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

Generating meta data for a formal abstract. 
-/

import data.buffer.parser
import group_theory.mathieu_group
import group_theory.euclidean_lattice
import group_theory.sporadic_group 
import tactic.tidy
-- import group_theory.lie_type

open tactic expr interactive nat native name list lean.parser pexpr


/--Takes an expr and spits out a list of all the names in that expr -/
meta def list_names (e : expr): list name :=
e.fold [] (λ e _ es, if is_constant e then insert e.const_name es else es)

meta structure meta_data (n : name):=
(type : expr)
(value : expr)
(informal : string)
(depends : list name)
(position : string)


meta def show_pos (n : name) : tactic string :=
do env   ← get_env,
   pos   ← returnopt (env.decl_pos n),
   olean ← returnopt (env.decl_olean n) <|> return "current file",
   pure $ to_string n ++ " was defined at " ++ olean ++ " : " ++ to_string pos.1 ++ ":" ++ to_string pos.2

/- -/
meta def gen_metadata (n : name) : tactic (meta_data n) :=
do 
    resolved ← resolve_constant n, 
    informal ← doc_string n,
    d ← get_decl resolved <|> fail ("could not retrieve given declration"),
    let type := d.type,
    let value := d.value,
    let depends := list_names d.type,
    docstring ← doc_string n, 
    position ← show_pos n,
    pure $ meta_data.mk n type value informal depends position

meta def trace_metadata (n : name) : tactic unit :=
do f ← gen_metadata n,
    tactic.trace "Type: ",
    tactic.trace f.type,
    tactic.trace "  ",
    tactic.trace "Value: ",
    tactic.trace f.value,
    tactic.trace " ",
    tactic.trace "Informal statement: ",
    tactic.trace f.informal,
    tactic.trace " ",
    tactic.trace "Dependencies: ",
    tactic.trace f.depends,
    tactic.trace " ",
    tactic.trace "Position: ",
    tactic.trace f.position,
    tactic.trace " "

/- Tests -/
#check environment.is_structure
run_cmd trace_metadata `mathieu_group.Aut
run_cmd trace_metadata `euclidean_space_canonical_inclusion
run_cmd trace_metadata `determinant_spec 
-- run_cmd trace_metadata `dynkin_diagram

