/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

The fabstract user attribute. 
-/

import tactic.basic 
import tactic.ext 

open interactive interactive.types lean.parser tactic native

-- #check name_map
@[user_attribute]
meta def fabstract_attr : user_attribute (rb_map name (list name)) (list name) :=
{
  name := `fabstract,
  descr := "The fabstract user attribute. Used to mark lemmas captured and also to store the 2010 MSC classification.",
  parser := list_of ident,
  cache_cfg := ⟨ λ l, l.mfoldl (λ m n, do
      tags ← fabstract_attr.get_param n,
      return $ tags.foldl (λ m t, m.insert_cons t n) m) mk_rb_map
   , [] ⟩
  -- cache_cfg := ⟨ λ l, l.mfoldl (λ m n, do
  --     d ← get_decl n, 
  --     v ← fabstract_attr.get_param n,
  --     return (m.insert n v)) mk_rb_map
  --  , [] ⟩ 
} 

/-- Well, hello there! -/
@[fabstract [ABC000,ABC200]] 
def test₁ : 1+1 =2 := by simp

@[fabstract [ABC101,ABC200]] 
def test₂ : 1+1 =2 := by simp

@[fabstract [ABC101,XYZ200]] 
def welp : 1+1 =2 := by simp

@[fabstract [JBX190,AXX200]] 
def woolp : 1+1 =2 := by simp

/- TODO: fix this garbage. -/
@[fabstract[]] 
def flump : 1+1 =2 := by simp

run_cmd attribute.get_instances `fabstract >>= tactic.trace

meta def get_MSC_codes (n : name) : tactic (list name) := user_attribute.get_param fabstract_attr n

run_cmd doc_string `test₁ >>= tactic.trace >>                  get_MSC_codes `test₁ >>= tactic.trace 

/- Gives all declarations with a particular MSC code.-/
run_cmd do 
  m ← fabstract_attr.get_cache,
  v ← m.find `ABC101,
  trace v