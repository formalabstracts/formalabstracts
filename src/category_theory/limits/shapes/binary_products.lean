-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison

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

end binary_product

def dfin.map {n : ℕ} (v : dvector C n) : dfin n → C :=
 λ d, by {induction v, cases d, from v_x}

-- variable [has_limit (@functor.of_function C _ _ $ dfin.map Xs)]


def finitary_product {n : ℕ} {Xs : dvector C n} [has_limit (functor.of_function $ dfin.map Xs)] : C :=
  limit (@functor.of_function C _ _ (dfin.map Xs))

/- Testing this definition -/
-- omit 𝒞 
-- def dfin.map' {n : ℕ} {α : Type*} : dvector α n → dfin n → α :=
--   λ v d, by {induction v, cases d, cases d, exact v_x, exact v_ih d_a}

-- def my_example := dfin.map' ([1,2,3] : dvector ℕ 3)

-- #eval my_example 0
-- #eval my_example 1
-- #eval my_example 2




namespace finitary_product

end finitary_product

end category_theory.limits
