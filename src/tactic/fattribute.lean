/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

The fabstract user attribute. 
-/

import tactic.basic 
import tactic.ext 

open interactive interactive.types lean.parser tactic native

@[user_attribute]
meta def fabstract_attr : user_attribute (rb_map name (list name)) (list name) :=
{
  name := `fabstract,
  descr := "The fabstract user attribute. Used to mark lemmas captured and also to store the 2010 MSC classification.",
  parser := many ident <|> pure [],
  cache_cfg := ⟨ λ l, l.mfoldl (λ m n, do
      tags ← fabstract_attr.get_param n,
      return $ tags.foldl (λ m t, m.insert_cons t n) m) mk_rb_map
   , [] ⟩
} 

/-- Well, hello there! -/
@[fabstract] 
def test₁ : 1+1 =2 := by simp

@[fabstract] 
def steiner_system : 1+1 =2 := by simp

def steiner_system_help : 1+1 =2 := by simp

@[fabstract JBX190 AXX200] 
def woolp : 1+1 =2 := by simp

@[fabstract] 
def flump : 1+1 =2 := by simp

meta def get_MSC_codes (n : name) : tactic (list name) := user_attribute.get_param fabstract_attr n

/- Tests -/
run_cmd attribute.get_instances `fabstract >>= tactic.trace
run_cmd doc_string `test₁ >>= tactic.trace >> get_MSC_codes `test₁ >>= tactic.trace 

/- Gives all declarations with a particular MSC code.-/
run_cmd do 
  m ← fabstract_attr.get_cache,
  v ← m.find `ABC101,
  trace v