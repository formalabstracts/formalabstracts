/-
Copyright (c) 2018 Koundinya Vajjha. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Koundinya Vajjha

A meta def called `direct_dependencies` which gives the names of all the theorems a given definition/theorem depends on.
-/

import measure_theory.probability_theory
import measure_theory.lebesgue_measure

open tactic expr
universe u

variables {s : Type u} [probability_space s] (p : probability_measure s) (a : set s)

def is_random_variable (X : s → ℝ) := measurable X

def indicator (a : set s) [decidable_pred a]:=(λ x : s, if x ∈ a then (1:ℝ) else 0)

meta def list_names (e : expr): list name :=
e.fold [] (λ e _ es, if is_constant e then insert e.const_name es else es)

meta def direct_dependencies : tactic unit :=
do  t ← tactic.target,
    let k := list_names t,
    -- pure $ to_string k
    tactic.trace k

lemma indicator_in (a  : set s) (x : s) [decidable_pred a]
(h : x ∈ a) : indicator a x = 1  :=
begin
direct_dependencies,
end

theorem foo : 1+1 = 2 :=
begin
direct_dependencies,
end
