/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

The fabstract user attribute. 
-/

import tactic.basic 
import tactic.ext 
import tactic.linenumber

open interactive interactive.types lean.parser tactic native

@[user_attribute]
meta def fabstract_attr : user_attribute (rb_map name (list name)) (list name) :=
{
  name := `fabstract,
  descr := "The fabstract user attribute. Used to mark lemmas captured in order to capture meta data.",
  parser := many ident <|> pure [],
  cache_cfg := ⟨ λ l, l.mfoldl (λ m n, do
      tags ← fabstract_attr.get_param n,
      return $ tags.foldl (λ m t, m.insert_cons t n) m) mk_rb_map
   , [] ⟩
} 

@[user_attribute]
meta def fabstract_attr' : user_attribute (list string) (list name) :=
{
  name := `fabstract',
  descr := "The fabstract user attribute. Used to mark lemmas captured in order to capture meta data.",
  parser := many ident <|> pure [],
  cache_cfg := ⟨ λ ns, mmap (trace_metadata_JSON) ns
   , [] ⟩
}
/-- Well, hello there! -/
@[fabstract' ABC000 ABC200] 
def test₁ : 1+1 =2 := by simp

@[fabstract' ABC101 ABC200] 
def test₂ : 1+1 =2 := by simp

@[fabstract ABC101 XYZ200] 
def welp : 1+1 =2 := by simp

@[fabstract' JBX190 AXX200] 
def woolp : 1+1 =2 := by simp

@[fabstract'] 
def flump : 1+1 =2 := by simp

meta def get_MSC_codes (n : name) : tactic (list name) := user_attribute.get_param fabstract_attr n

/- Tests -/
run_cmd attribute.get_instances `fabstract' >>= tactic.trace
-- run_cmd doc_string `test₁ >>= tactic.trace >> get_MSC_codes `test₁ >>= tactic.trace 

/- Gives all declarations with a particular MSC code.-/
run_cmd do 
  m ← fabstract_attr'.get_cache,
  -- v ← m.find `ABC101,
  trace m

@[user_attribute]
meta def foo_attr : user_attribute string :=
{ name     := `foo, descr := "bar",
  cache_cfg := {
    mk_cache := λ ns, return $ string.join (list.map (λ n, to_string n ++ "\n") ns),
    dependencies := []} }

attribute [foo] eq.refl eq.mp

set_option trace.user_attributes_cache true

run_cmd do
  s : string ← foo_attr.get_cache,
  tactic.trace s,
  s : string ← foo_attr.get_cache,
  tactic.trace s,
  foo_attr.set `eq.mpr () tt,
  s : string ← foo_attr.get_cache,
  tactic.trace s,
  tactic.set_basic_attribute `reducible ``eq.mp, -- should not affect [foo] cache
  s : string ← foo_attr.get_cache,
tactic.trace s