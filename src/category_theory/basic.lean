import category_theory.category tactic.omitted

@[obviously] meta def obviously_omitted : tactic unit := tactic.interactive.omitted

open category_theory
universes v u
variables {C : Type u} [h : category.{v} C] {X Y Z : C}
include h

def factors_through (f : X ⟶ Z) (g : Y ⟶ Z) : Prop :=
∃(h : X ⟶ Y), f = h ≫ g