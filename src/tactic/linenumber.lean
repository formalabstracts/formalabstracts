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
import tactic.explode
import .depends
-- import system.io
-- import group_theory.lie_type

open tactic expr interactive nat native name list


meta structure meta_data (n : name):=
(type : expr)
(value : expr)
(informal : string)
(typedepends : list name)
(valdepends : list name)
(position : string)


meta def show_pos (n : name) : tactic string :=
do env   ← get_env,
   pos   ← returnopt (env.decl_pos n),
   olean ← returnopt (env.decl_olean n) <|> return "current file",
   pure $ to_string n ++ " was defined at " ++ olean ++ " : " ++ to_string pos.1 ++ ":" ++ to_string pos.2

/-TODO(Kody): What about structures? (A. Use is_structure)
            What about instances? (A. Anything that is not a thm, ax, defn, lemma, structure?)-/
meta def gen_metadata (n : name) : tactic (meta_data n) :=
do 
    resolved ← resolve_constant n, 
    informal ← doc_string n <|> return " ",
    d ← get_decl resolved <|> fail ("could not retrieve given declration"),
    let type := d.type,
    let value := d.value,
    typedepends ← name_dir_deps n,
    valdepends ← name_dir_deps_val n,
    position ← show_pos n,
    pure $ meta_data.mk n type value informal typedepends valdepends position

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
    tactic.trace "Type Dependencies: ",
    tactic.trace f.typedepends,
    tactic.trace " ",
    tactic.trace "Value Dependencies: ",
    tactic.trace f.valdepends,
    tactic.trace " ",
    tactic.trace "Position: ",
    tactic.trace f.position,
    tactic.trace " "

-- namespace JSON

-- end JSON 

run_cmd trace_metadata `mathieu_group.Aut
run_cmd trace_metadata `euclidean_space_canonical_inclusion
run_cmd trace_metadata `nat.rec_on
run_cmd trace_metadata `mathieu_group.steiner_system
run_cmd trace_metadata `J4

-- run_cmd trace_metadata `dynkin_diagram
#check mathieu_group.steiner_system_fintype

#check name