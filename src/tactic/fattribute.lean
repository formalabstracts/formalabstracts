/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

The fabstract user attribute. 
-/

import tactic.basic 
import tactic.ext 

open interactive interactive.types lean.parser tactic

@[user_attribute]
meta def fabstract_attr : user_attribute unit (list name) :=
{
  name := `fabstract,
  descr := "The fabstract user attribute. Used to mark lemmas captured and also to store the 2010 MSC classification.",
  parser := list_of ident
} 

/-- Well, hello there! -/
@[fabstract [ABC000,ABC200]] 
def test : 1+1 =2 := by simp


meta def get_MSC_codes (n : name) : tactic (list name) := user_attribute.get_param fabstract_attr n

run_cmd doc_string `test >>= tactic.trace >>                   get_MSC_codes `test >>= tactic.trace 

