/-
Copyright (c) 2019 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

The fabstract user attribute.
-/

import tactic.metadata

open interactive interactive.types lean.parser tactic native 

@[user_attribute]
meta def fabstract_attr : user_attribute (rb_map name (string)) (list name) :=
{
  name := `fabstract,
  descr := "The fabstract user attribute. Used to mark lemmas captured in order to capture meta data.",
  parser := many ident <|> pure [],
  cache_cfg := ⟨
    λ ns, ( do l ← mmap (trace_metadata_JSON) ns,
         pure $ rb_map.of_list (list.zip ns l))
   , [] ⟩
}

/- Tests -/
/-- Well, hello there! -/
-- @[fabstract ABC000 ABC200]
def test₁ : 1+1 =2 := by simp

-- @[fabstract ABC101 ABC200]
def test₂ : 1+1 =2 := by simp

-- @[fabstract ABC101 XYZ200]
def welp : 1+1 =2 := by simp

@[fabstract JBX190 AXX200]
def woolp : 1+1 =2 := by simp

@[fabstract]
def flump : 1+1 =2 := by simp

meta def query_cache (n : name) : tactic (string) :=
do m ← fabstract_attr.get_cache,
  v ← m.find n,
  pure v

meta def prod_list_to_JSON {key : Type} {data : Type} [has_to_format data]: list (key × data) → string 
| [] :=  " "
| ((k,v) :: kvs) := if list.length kvs = 0 then to_string (format!"\"k\" :{v}}") else to_string (format!"{{\"k\" :{v},") ++ prod_list_to_JSON kvs

meta def rb_map_to_JSON {key : Type} {data : Type} [has_to_format data] (m : rb_map key data) : tactic string :=
pure $ prod_list_to_JSON $ rb_map.to_list m

-- run_cmd attribute.get_instances `fabstract >>= tactic.trace

-- run_cmd do
  -- m ← fabstract_attr.get_cache,
  -- l ← rb_map_to_JSON m,
  -- tactic.trace l,
  -- skip 

