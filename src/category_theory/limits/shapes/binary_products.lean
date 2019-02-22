-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Jesse Han

import category_theory.limits.shapes.products basic data.dvector

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

universes u v

open category_theory

namespace category_theory.limits

@[derive decidable_eq] inductive two : Type v
| left | right

def two.map {C : Type u} (X Y : C) : two → C
| two.left := X
| two.right := Y

variables {C : Type u} [𝒞 : category.{v u} C]
include 𝒞 

variables {X Y : C}

def binary_fan {P : C} (π₁ : P ⟶ X) (π₂ : P ⟶ Y) : fan (two.map X Y) :=
{ X := P,
  π := ⟨λ j, two.cases_on j π₁ π₂, λ x y f, by tidy⟩}
def binary_cofan {P : C} (ι₁ : X ⟶ P) (ι₂ : Y ⟶ P) : cofan (two.map X Y) :=
{ X := P,
  ι := { app := λ j, two.cases_on j ι₁ ι₂ }}

def fan.π₁ {f : two → C} (t : fan f) : t.X ⟶ f two.left := t.π.app two.left
def fan.π₂ {f : two → C} (t : fan f) : t.X ⟶ f two.right := t.π.app two.right

def cofan.ι₁ {f : two → C} (t : cofan f) : f two.left ⟶ t.X := t.ι.app two.left
def cofan.ι₂ {f : two → C} (t : cofan f) : f two.right ⟶ t.X := t.ι.app two.right

-- #check limit

-- #print has_limit

/- functor.of_function (two.map X Y) is the binary product diagram -/

/-- The binary product is the vertex of the limiting cone to the canonical functor two → 𝒞
    associated to X and Y -/
def binary_product (X Y : C) [has_limit (functor.of_function $ two.map X Y)] : C :=
  limit (functor.of_function $ two.map X Y)

namespace binary_product
def π₁ {X Y : C} [has_limit (functor.of_function $ two.map X Y)] : binary_product X Y ⟶ X := limit.π _ two.left

def π₂ {X Y : C} [has_limit (functor.of_function $ two.map X Y)] : binary_product X Y ⟶ Y := limit.π _ two.right

local infix ` × `:60 := binary_product

def dfin.map {n : ℕ} : dvector C n → dfin n → C :=
  λ v d, by {induction v, cases d, cases d, exact v_x, exact v_ih d_a}

example {X : C} [has_limits C] : X × X × X = (X × X) × X := by refl

variable [has_limits C]

def exchange_coordinates {X Y : C} [has_limits C] : X × Y ⟶ X × X := sorry

-- def reassoc {X : C} [has_limits C] : iso ((X × X) × X) (X × (X × X)) :=
-- { hom := _,
--   inv := _,
--   hom_inv_id' := _,
--   inv_hom_id' := _ }

-- structure group_object : Type (max u v) :=
-- (carrier : C)
-- (mul : (carrier × carrier) ⟶ carrier)
-- (mul_assoc)
-- (one)
-- (one_mul)
-- (mul_one)
-- (inv)
-- (mul_left_inv)


end binary_product

-- 64:1: @[class, priority 100, to_additive name.mk_string "add_group" name.anonymous]
-- structure group : Type u → Type u
-- fields:
-- group.mul : Π {α : Type u} [c : group α], α → α → α
-- group.mul_assoc : ∀ {α : Type u} [c : group α] (a b c_1 : α), a * b * c_1 = a * (b * c_1)
-- group.one : Π (α : Type u) [c : group α], α
-- group.one_mul : ∀ {α : Type u} [c : group α] (a : α), 1 * a = a
-- group.mul_one : ∀ {α : Type u} [c : group α] (a : α), a * 1 = a
-- group.inv : Π {α : Type u} [c : group α], α → α
-- group.mul_left_inv : ∀ {α : Type u} [c : group α] (a : α), a⁻¹ * a = 1

-- variable [has_limit (@functor.of_function C _ _ $ dfin.map Xs)]

/- Testing this definition -/
-- omit 𝒞 
-- def dfin.map' {n : ℕ} {α : Type*} : dvector α n → dfin n → α :=
--   λ v d, by {induction v, cases d, cases d, exact v_x, exact v_ih d_a}

-- def my_example := dfin.map' ([1,2,3] : dvector ℕ 3)

-- #eval my_example 0
-- #eval my_example 1
-- #eval my_example 2

def finitary_product {n : ℕ} (Xs : dvector C n)
  [has_limit (functor.of_function $ dfin.map Xs)] : C :=
  limit (@functor.of_function C _ _ (dfin.map Xs))

namespace finitary_product
def π_nth (m : ℕ) {n : ℕ} (h : m < n) {Xs : dvector C n} [has_limit (functor.of_function $ dfin.map Xs)] : finitary_product Xs ⟶ (Xs.nth m h) :=
  by {convert (limit.π (functor.of_function $ dfin.map Xs) (dfin.of_fin ⟨m,h⟩)), from omitted}

/- TODO(jesse) this should say that there is a cone isomorphism between the binary product of two objects, and the binary product induced by the finitary product induced by the map from dfin 2 → C -/
lemma binary_finitary_product {X Y : C} : sorry := sorry

-- actually, maybe for general group objects, what we want is an association isomorphism between iterated binary products... hmm...

end finitary_product

end category_theory.limits
