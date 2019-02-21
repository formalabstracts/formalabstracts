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
import measure_theory.giry_monad
-- import system.io
-- import group_theory.lie_type

open tactic expr interactive nat native name list environment


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
    -- to_string n ++ " was defined at " ++
   pure $  olean ++ " : " ++ to_string pos.1 ++ ":" ++ to_string pos.2

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

def squash_linebreak (s : string) : string :=
list.foldr  (++) ""  $ list.map (λ h, if h = '\n' then "" else to_string h) (s.to_list)

/-TODO:1) Make this more general (arbitrary structure fields + values).
2) Make this more comprehensive (include `meta`, `noncomputable` information) 
-/
meta def trace_metadata_JSON (n : name) : tactic string := 
do  env ← get_env, 
    f ← gen_metadata n,
    fields ← returnopt $ structure_fields env `meta_data,
    -- tactic.trace $ map () fields,
    pptype ← pp f.type,
    sppval ← pp f.value,
    let jsanitype := squash_linebreak $ format.to_string pptype,
    let jsanival := squash_linebreak $ format.to_string sppval,
    let jinformal := squash_linebreak f.informal,
    let tdeps := (do m ← f.typedepends, pure $ squash_linebreak $ to_string m),
    let jtdeps := squash_linebreak $ to_string tdeps,
    let vdeps := (do m ← f.valdepends, pure $ squash_linebreak $ to_string m),
    let jvdeps := squash_linebreak $ to_string vdeps,
    -- tactic.trace vdeps,
    let pos := f.position,
    -- skip
    pure $ to_string format!"{{\"Type\" :\"{jsanitype}\",\n\"Docstring\" :\"{jinformal}\",\n\"Value\":\"{jsanival}\",\n\"Type Dependencies\":\"{jtdeps}\",\n\"Value Dependencies\":\"{jvdeps}\",\n\"Position\":\"{pos}\"\n }"

/- Tests -/
run_cmd trace_metadata `mathieu_group.Aut
run_cmd trace_metadata `euclidean_space_canonical_inclusion
run_cmd trace_metadata `nat.rec_on
/- Example of a metadata trace on a structure -/
run_cmd trace_metadata `mathieu_group.steiner_system
/- Example of a metadata trace on an instance -/
run_cmd trace_metadata `mathieu_group.steiner_system_fintype
run_cmd trace_metadata `J4
run_cmd trace_metadata `mathieu_group.steiner_system_fintype
-- run_cmd trace_metadata `dynkin_diagram
#check mathieu_group.steiner_system_fintype
run_cmd trace_metadata_JSON `J4
run_cmd trace_metadata_JSON `mathieu_group.steiner_system_fintype
run_cmd trace_metadata_JSON `nat.rec_on
run_cmd trace_metadata_JSON `measure_theory.lintegral_supr_directed >>= tactic.trace

-- #eval range 100
#depends measure_theory.lintegral_supr_directed
#eval list.repeat 3 3
def long_lists (m : ℕ) : list (list ℕ) := 
do l ← list.repeat m 10,
    pure [l]

#help options
#help commands
