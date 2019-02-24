-- Copyright (c) 2018 Scott Morrison. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Scott Morrison, Jesse Han

import category_theory.limits.shapes.products basic data.dvector category_theory.limits.limits

universes u v

open category_theory

namespace category_theory.limits

@[derive decidable_eq] inductive two : Type v
| left | right

def two.map {C : Type u} (X Y : C) : two → C
| two.left := X
| two.right := Y

def two.functor {C : Type u} (X Y : C) [category C] : (discrete two) ⥤ C :=
functor.of_function (two.map X Y)

def empty.functor (C : Type u) [category C] : (discrete pempty) ⥤ C :=
functor.of_function (λ x, by {cases x} : pempty → C)

def empty_cone {C} [category C] (A : C) : limits.cone (empty.functor C) :=
{ X := A,
  π := { app := λ x, by cases x,
  naturality' := by tidy}}

def commutative_square {C : Type u} [category.{v u} C] {A B A' B' : C}
  (f_top : A ⟶ B) (d_left : A ⟶ A') (d_right : B ⟶ B') (f_bot : A' ⟶ B') :=
f_top ≫ d_right = d_left ≫ f_bot

-- /- f_comp is the composition f₁ ≫ f₂ -/
-- def commutative_triangle {C : Type u} [category C] {A₁ A₂ A₃ : C}
--     (f_comp : A₁ ⟶ A₃) (f₁ : A₁ ⟶ A₂) (f₂ : A₂ ⟶ A₃) :=
-- f_comp = f₁ ≫ f₂

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

def binary_product (X Y : C) [has_limit $ two.functor X Y] : C :=
  limit (two.functor X Y)

namespace binary_product
def π₁ {X Y : C} [has_limit $ two.functor X Y] : binary_product X Y ⟶ X := limit.π _ two.left

def π₂ {X Y : C} [has_limit $ two.functor X Y] : binary_product X Y ⟶ Y := limit.π _ two.right

local infix ` × `:60 := binary_product

def dfin.map {n : ℕ} : dvector C n → dfin n → C :=
  λ v d, by {induction v, cases d, cases d, exact v_x, exact v_ih d_a}

example {X : C} [has_limits_of_shape (discrete two) C] : X × X × X = (X × X) × X := by refl

-- @[unify] def hewwo {A A' : C} {F : (discrete two) ⥤ C} {t : limits.cone F} : unification_hint :=
-- { pattern := (A × A') ≟ (t.X),
--   constraints := [(t.X) ≟ (limits.limit F)]
--   }
-- -- , F ≟ (functor.of_function (two.map A A')), t ≟ (limit.cone F)]

-- @[unify] def hewwo' {A A' B B' X Y : C} : unification_hint :=
-- { pattern := ((A × A') ⟶ (B × B')) ≟ (X ⟶ Y),
--   constraints := [A × A' ≟ X, B × B' ≟ Y]}

def cone_of_two_maps {W A₁ A₂: C} (f₁ : W ⟶ A₁) (f₂ : W ⟶ A₂) : cone (two.functor A₁ A₂) :=
{ X := W,
  π := { app := λ l, two.rec_on l f₁ f₂,
  naturality' := by tidy}}

lemma cone_of_two_maps_object [has_limits_of_shape (discrete two) C] {B₁ B₂ A₁ A₂: C} {f₁ : B₁ × B₂ ⟶ A₁} {f₂ : B₁ × B₂ ⟶ A₂}
  : (cone_of_two_maps f₁ f₂).X = B₁ × B₂ := by refl

def map_to_product.mk [has_limits_of_shape (discrete two) C]{W B₁ B₂ : C} (f₁ : W ⟶ B₁) (f₂ : W ⟶ B₂) : W ⟶ B₁ × B₂ :=
  is_limit.lift (limit.is_limit $ two.functor B₁ B₂) (cone_of_two_maps f₁ f₂)

def binary_product.map [has_limits_of_shape (discrete two) C] {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') : A × B ⟶ A' × B' :=
  map_to_product.mk (π₁ ≫ f) (π₂ ≫ g)

local infix ` ×.map `:60 := binary_product.map

def reassoc_hom [has_limits_of_shape (discrete two) C] (X : C) : ((X × X) × X) ⟶ (X × (X × X)) :=
  map_to_product.mk (π₁ ≫ π₁) (π₂ ×.map (𝟙 X))

def reassoc_inv [has_limits_of_shape (discrete two) C] (X : C) : (X × (X × X)) ⟶ ((X × X) × X) :=
  map_to_product.mk ((𝟙 X) ×.map π₁)(π₂ ≫ π₂)

def reassoc_iso [has_limits_of_shape (discrete two) C] (X : C) : iso ((X × X) × X) (X × (X × X)) :=
{ hom := reassoc_hom X,
  inv := reassoc_inv X,
  hom_inv_id' := omitted,
  inv_hom_id' := omitted} 

example :
  commutative_square
         /-unit-/ (𝟙 unit) /- unit  -/
         (𝟙 unit)            (𝟙 unit)
         /-unit-/ (𝟙 unit) /- unit -/
  := by tidy

def terminal_object [@has_limits_of_shape (discrete pempty) (by apply_instance) C 𝒞] : C
  := limit (functor.of_function (λ x, by {cases x} : pempty → C))

-- instance has_one_term {D} [category D] [has_limits_of_shape (discrete pempty) D] : has_one D :=
-- ⟨terminal_object⟩

notation `term` := terminal_object

def terminal_map [has_limits_of_shape (discrete pempty) C] (A : C) : A ⟶ term :=
(is_limit.lift (limit.is_limit (empty.functor C)) (empty_cone A))

lemma mul_one [has_limits C] (G : C) : nonempty $ iso (term × G) G := omitted

lemma one_mul [has_limits C] (G : C) : nonempty $ iso (G × term) G := omitted

-- noncomputable def mul_one_hom [has_limits C] (G : C) : (term × G) ⟶ G :=
-- (classical.choice $ mul_one G).hom

-- noncomputable def one_mul_hom [has_limits C] (G : C) : (G × term) ⟶ G :=
-- (classical.choice $ (one_mul G)).hom

def mul_one_inv [has_limits C] (G : C) : G ⟶ (G × term) :=
  map_to_product.mk (𝟙 _) (terminal_map G)

def one_mul_inv [has_limits C] (G : C) : G ⟶ (term × G) :=
  map_to_product.mk (terminal_map G) (𝟙 _)

end binary_product

/- TODO(jesse) revisit later -/

-- variable [has_limit (@functor.of_function C _ _ $ dfin.map Xs)]

/- Testing this definition -/
-- omit 𝒞 
-- def dfin.map' {n : ℕ} {α : Type*} : dvector α n → dfin n → α :=
--   λ v d, by {induction v, cases d, cases d, exact v_x, exact v_ih d_a}

-- def my_example := dfin.map' ([1,2,3] : dvector ℕ 3)

-- #eval my_example 0
-- #eval my_example 1
-- #eval my_example 2

-- def finitary_product {n : ℕ} (Xs : dvector C n)
--   [has_limit (functor.of_function $ dfin.map Xs)] : C :=
--   limit (@functor.of_function C _ _ (dfin.map Xs))

-- namespace finitary_product
-- def π_nth (m : ℕ) {n : ℕ} (h : m < n) {Xs : dvector C n} [has_limit (functor.of_function $ dfin.map Xs)] : finitary_product Xs ⟶ (Xs.nth m h) :=
--   by {convert (limit.π (functor.of_function $ dfin.map Xs) (dfin.of_fin ⟨m,h⟩)), from omitted}

-- /- TODO(jesse) this should say that there is a cone isomorphism between the binary product of two objects, and the binary product induced by the finitary product induced by the map from dfin 2 → C -/
-- lemma binary_finitary_product {X Y : C} : sorry := sorry

-- -- actually, maybe for general group objects, what we want is an association isomorphism between iterated binary products... hmm...

-- end finitary_product

end category_theory.limits
