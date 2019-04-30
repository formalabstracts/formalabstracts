-- Copyright (c) 2018 Jesse Han. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jesse Han

import category_theory.limits.shapes.products basic data.dvector
       category_theory.limits.shapes.equalizers
       category_theory.limits.limits

universes u v

open category_theory

namespace category_theory.limits

@[derive decidable_eq] inductive two : Type u
| left | right

def two.map {C : Type*} (X Y : C) : two → C
| two.left := X
| two.right := Y

def two.functor {C : Type u} (X Y : C) [category.{v u} C] : (discrete two) ⥤ C :=
functor.of_function (two.map X Y)

def empty.functor (C : Type*) [category C] : (discrete pempty) ⥤ C :=
functor.of_function (λ x, by {cases x} : pempty → C)

def empty_cone {C : Type u} [category.{v u} C] (A : C) : limits.cone (empty.functor C) :=
{ X := A,
  π := { app := λ x, by cases x,
  naturality' := by tidy}}

def commutative_square {C : Type u} [category.{v u} C] {A B A' B' : C}
  (f_top : A ⟶ B) (d_left : A ⟶ A') (d_right : B ⟶ B') (f_bot : A' ⟶ B') :=
f_top ≫ d_right = d_left ≫ f_bot

variables {C : Type u} [𝒞 : category.{v u} C]
include 𝒞

variable(C)
@[class] def has_binary_products := has_limits_of_shape (discrete two) C
@[class] def has_terminal_object : Type* := has_limits_of_shape (discrete pempty) C

@[class] def has_binary_coproducts := has_colimits_of_shape (discrete two) C
@[class] def has_initial_object : Type* := has_colimits_of_shape (discrete pempty) C

@[instance] def has_limit_two_of_has_binary_products [H : has_binary_products C] {X Y : C} :
  has_limit $ two.functor X Y :=
H (two.functor _ _)

@[instance] def has_limit_empty_of_has_terminal_object [H : has_terminal_object C] :
  has_limit $ empty.functor C :=
H (empty.functor C)

variable{C}

/-- The binary product is the vertex of the limiting cone to the canonical functor two → 𝒞
    associated to X and Y -/
def binary_product (X Y : C) [has_limit $ two.functor X Y] : C :=
limit (two.functor X Y)

namespace binary_product
local infix ` × `:60 := binary_product

def π₁ {X Y : C} [has_limit $ two.functor X Y] : X × Y ⟶ X := limit.π _ two.left

def π₂ {X Y : C} [has_limit $ two.functor X Y] : X × Y ⟶ Y := limit.π _ two.right

def dfin.map {n : ℕ} : dvector C n → dfin n → C :=
λ v d, by {induction v, cases d, cases d, exact v_x, exact v_ih d_a}

example {X : C} [has_binary_products C] : X × X × X = (X × X) × X := by refl

def cone_of_two_maps {W A₁ A₂: C} (f₁ : W ⟶ A₁) (f₂ : W ⟶ A₂) : cone (two.functor A₁ A₂) :=
{ X := W,
  π := { app := λ l, two.rec_on l f₁ f₂,
  naturality' := by tidy}}

lemma cone_of_two_maps_object [has_binary_products C] {B₁ B₂ A₁ A₂: C} {f₁ : B₁ × B₂ ⟶ A₁}
  {f₂ : B₁ × B₂ ⟶ A₂} : (cone_of_two_maps f₁ f₂).X = B₁ × B₂ := by refl

def map_to_product.mk {H : has_binary_products C} {W B₁ B₂ : C} (f₁ : W ⟶ B₁) (f₂ : W ⟶ B₂) :
  W ⟶ B₁ × B₂ :=
is_limit.lift (limit.is_limit _) (cone_of_two_maps f₁ f₂)

def binary_product.map {H : has_binary_products C} {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') :
  A × B ⟶ A' × B' :=
map_to_product.mk (π₁ ≫ f) (π₂ ≫ g)

local infix ` ×.map `:60 := binary_product.map

def reassoc_hom {H : has_binary_products C} (X : C) : ((X × X) × X) ⟶ (X × (X × X)) :=
by apply map_to_product.mk (π₁ ≫ π₁) (π₂ ×.map (𝟙 X))

def reassoc_inv {H : has_binary_products C} (X : C) : (X × (X × X)) ⟶ ((X × X) × X) :=
by apply  map_to_product.mk ((𝟙 X) ×.map π₁)(π₂ ≫ π₂)

def reassoc_iso {H : has_binary_products C} (X : C) : iso ((X × X) × X) (X × (X × X)) :=
{ hom := by apply reassoc_hom X,
  inv := by apply reassoc_inv X,
  hom_inv_id' := omitted,
  inv_hom_id' := omitted}

example :
  commutative_square
         /-unit-/ (𝟙 unit) /- unit  -/
         (𝟙 unit)            (𝟙 unit)
         /-unit-/ (𝟙 unit) /- unit -/
  := by tidy


section terminal_object

def terminal_object [has_terminal_object C] : C :=
limit (empty.functor C)

notation `term` := terminal_object

def terminal_map [has_terminal_object C] (A : C) : A ⟶ term :=
is_limit.lift (limit.is_limit (empty.functor C)) (empty_cone A)

lemma mul_one [has_terminal_object C] [has_binary_products C] (G : C) :
  nonempty $ iso (term × G) G := omitted

lemma one_mul [has_terminal_object C] [has_binary_products C] (G : C) :
  nonempty $ iso (G × term) G := omitted

def mul_one_inv [has_terminal_object C] [has_binary_products C] (G : C) : G ⟶ G × term :=
by apply map_to_product.mk (𝟙 _) (terminal_map G)

def one_mul_inv [has_terminal_object C] [has_binary_products C] (G : C) : G ⟶ term × G :=
by apply map_to_product.mk (terminal_map G) (𝟙 _)

end terminal_object

end binary_product

namespace finite_limits
open binary_product

instance fintype_two : fintype two :=
{elems := { val := ⟦[two.left, two.right]⟧,
  nodup := by tidy },
  complete := λ x, by cases x; tidy}

example : fintype pempty := by apply_instance

section finite_products

variable (C)
@[class]def has_finite_products := Π α : Type*, (fintype α) → has_limits_of_shape (discrete α) C

@[class]def has_equalizers := has_limits_of_shape (walking_pair) C

def has_binary_products_of_has_finite_products [H : has_finite_products C] :
  has_binary_products C := H _ $ by apply_instance
attribute [instance] has_binary_products_of_has_finite_products

@[instance]def has_terminal_object_of_has_finite_products [H : has_finite_products C] :
  has_limits_of_shape (discrete pempty) C := H _ $ by apply_instance

@[class]def has_finite_limits := (@has_finite_products C 𝒞) × (@has_equalizers C 𝒞)

end finite_products

end finite_limits

end category_theory.limits
