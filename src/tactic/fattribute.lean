/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

The fabstract user attribute.
-/

import tactic.basic
import tactic.metadata

open interactive interactive.types lean.parser tactic native

-- @[user_attribute]
-- meta def fabstract_attr : user_attribute (rb_map name (list name)) (list name) :=
-- {
--   name := `fabstract,
--   descr := "The fabstract user attribute. Used to mark lemmas captured in order to capture meta data.",
--   parser := many ident <|> pure [],
--   cache_cfg := ⟨ λ l, l.mfoldl (λ m n, do
--       tags ← fabstract_attr.get_param n,
--       return $ tags.foldl (λ m t, m.insert_cons t n) m) mk_rb_map
--    , [] ⟩
-- }

@[user_attribute]
meta def fabstract_attr : user_attribute (rb_map name (string)) (list name) :=
{
  name := `fabstract,
  descr := "The fabstract user attribute. Used to mark lemmas captured in order to capture meta data.",
  parser := many ident <|> pure [],
  cache_cfg := ⟨
    λ ns, ( do l ← mmap (trace_metadata_JSON) ns, pure $ rb_map.of_list (list.zip ns l))
   , [] ⟩
}

/- Tests -/
/-- Well, hello there! -/
@[fabstract ABC000 ABC200]
def test₁ : 1+1 =2 := by simp

@[fabstract ABC101 ABC200]
def test₂ : 1+1 =2 := by simp

@[fabstract ABC101 XYZ200]
def welp : 1+1 =2 := by simp

@[fabstract JBX190 AXX200]
def woolp : 1+1 =2 := by simp

@[fabstract]
def flump : 1+1 =2 := by simp

meta def query_cache (n : name) : tactic (string) :=
do m ← fabstract_attr.get_cache,
  v ← m.find n,
  pure v

-- run_cmd attribute.get_instances `fabstract >>= tactic.trace

-- run_cmd do
--   m ← fabstract_attr.get_cache,
--   v ← m.find `flump,
--   trace m

