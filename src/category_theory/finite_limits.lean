-- Copyright (c) 2018 Jesse Han. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jesse Han

import .limits.shapes.products basic data.dvector
       .limits.shapes.equalizers
       category_theory.limits.limits

universes v u

open category_theory

namespace category_theory.limits

@[derive decidable_eq] inductive two : Type u
| left | right

def two.map {C : Sort*} (X Y : C) : two → C
| two.left := X
| two.right := Y

def two.functor {C : Sort u} (X Y : C) [category.{v+1} C] : discrete two ⥤ C :=
functor.of_function (two.map X Y)

def empty.functor (C : Sort*) [category.{v+1} C] : discrete pempty ⥤ C :=
functor.of_function (λ x, by {cases x} : pempty → C)

def empty_cone {C : Sort u} [category.{v+1} C] (A : C) : limits.cone (empty.functor C) :=
{ X := A,
  π := { app := λ x, by cases x,
  naturality' := by tidy}}

def commutative_square {C : Sort u} [category.{v u} C] {A B A' B' : C}
  (f_top : A ⟶ B) (d_left : A ⟶ A') (d_right : B ⟶ B') (f_bot : A' ⟶ B') :=
f_top ≫ d_right = d_left ≫ f_bot

variables {C : Type u} [𝒞 : category.{v+1} C]
include 𝒞

variable(C)
@[class] def has_binary_products := has_limits_of_shape (discrete two.{v}) C
@[class] def has_terminal_object : Sort* := has_limits_of_shape.{v} (discrete pempty) C

@[class] def has_binary_coproducts := has_colimits_of_shape (discrete two.{v}) C
@[class] def has_initial_object : Sort* := has_colimits_of_shape.{v} (discrete pempty) C

@[instance] def has_limit_two_of_has_binary_products [H : has_binary_products C] {X Y : C} :
  has_limit $ two.functor X Y :=
@has_limits_of_shape.has_limit _ _ _ _ H (two.functor X Y)

@[instance] def has_limit_empty_of_has_terminal_object [H : has_terminal_object C] :
  has_limit $ empty.functor C :=
@has_limits_of_shape.has_limit _ _ _ _ H (empty.functor C)

variable{C}

def has_terminal_object.mk (T : C) (h₁ : ∀(X : C), X ⟶ T)
  (h₂ : ∀{{X : C}} (f g : X ⟶ T), f = g) : has_terminal_object C :=
⟨λ F, { cone := ⟨T, ⟨pempty.rec _, pempty.rec _⟩⟩,
  is_limit :=
  { lift := λ s, h₁ s.X,
    fac' := λ s, pempty.rec _,
    uniq' := λ s m h, h₂ _ _ } }⟩

def has_binary_products.mk (m : C → C → C) (p1 : ∀{X Y : C}, m X Y ⟶ X)
  (p2 : ∀{X Y : C}, m X Y ⟶ Y) (lft : ∀{{X Y Z : C}} (f : Z ⟶ X) (g : Z ⟶ Y), Z ⟶ m X Y)
  (lft1 : ∀{{X Y Z : C}} (f : Z ⟶ X) (g : Z ⟶ Y), lft f g ≫ p1 = f)
  (lft2 : ∀{{X Y Z : C}} (f : Z ⟶ X) (g : Z ⟶ Y), lft f g ≫ p2 = g)
  (lft_unique : ∀{{X Y Z : C}} (f g : Z ⟶ m X Y) (h1 : f ≫ p1 = g ≫ p1) (h2 : f ≫ p2 = g ≫ p2),
    f = g) : has_binary_products C :=
begin
  constructor, intro F, fsplit,
  { use m (F.obj two.left) (F.obj two.right),
    apply nat_trans.of_homs, refine two.rec _ _, exact p1, exact p2 },
  refine limits.is_limit.mk _ _ _,
  { rintro ⟨X, f⟩, apply lft (f.app two.left), dsimp, exact f.app two.right },
  { rintro ⟨X, f⟩ (_|_), apply lft1, apply lft2 },
  { rintro ⟨X, f⟩ g h, dsimp, apply lft_unique,
    rw [lft1], exact h two.left, rw [lft2], exact h two.right }
end

def has_initial_object.mk (I : C) (h₁ : ∀(X : C), I ⟶ X)
  (h₂ : ∀{{X : C}} (f g : I ⟶ X), f = g) : has_initial_object C :=
⟨λ F, { cocone := ⟨I, ⟨pempty.rec _, pempty.rec _⟩⟩,
  is_colimit :=
  { desc := λ s, h₁ s.X,
    fac' := λ s, pempty.rec _,
    uniq' := λ s m h, h₂ _ _ } }⟩

def has_binary_coproducts.mk (p : C → C → C) (i1 : ∀{X Y : C}, X ⟶ p X Y)
  (i2 : ∀{X Y : C}, Y ⟶ p X Y) (dsc : ∀{{X Y Z : C}} (f : X ⟶ Z) (g : Y ⟶ Z), p X Y ⟶ Z)
  (dsc1 : ∀{{X Y Z : C}} (f : X ⟶ Z) (g : Y ⟶ Z), i1 ≫ dsc f g = f)
  (dsc2 : ∀{{X Y Z : C}} (f : X ⟶ Z) (g : Y ⟶ Z), i2 ≫ dsc f g = g)
  (dsc_unique : ∀{{X Y Z : C}} (f g : p X Y ⟶ Z) (h1 : i1 ≫ f = i1 ≫ g) (h2 : i2 ≫ f = i2 ≫ g),
    f = g) : has_binary_coproducts C :=
begin
  constructor, intro F, fsplit,
  { use p (F.obj two.left) (F.obj two.right),
    apply nat_trans.of_homs, refine two.rec _ _, exact i1, exact i2 },
  refine limits.is_colimit.mk _ _ _,
  { rintro ⟨X, f⟩, apply dsc (f.app two.left), dsimp, exact f.app two.right },
  { rintro ⟨X, f⟩ (_|_), apply dsc1, apply dsc2 },
  { rintro ⟨X, f⟩ g h, dsimp, apply dsc_unique,
    rw [dsc1], exact h two.left, rw [dsc2], exact h two.right }
end

/-- The binary product is the vertex of the limiting cone to the canonical functor two → 𝒞
    associated to X and Y -/
def binary_product (X Y : C) [has_limit $ two.functor X Y] : C :=
limit (two.functor X Y)

namespace binary_product

local infix ` × `:60 := binary_product

def π₁ {X Y : C} [has_limit $ two.functor X Y] : X × Y ⟶ X := limit.π _ two.left

def π₂ {X Y : C} [has_limit $ two.functor X Y] : X × Y ⟶ Y := limit.π _ two.right

/-- An alternative version of `π₁` if type-class inference fails -/
def π₁' {X Y : C} {H : has_binary_products C} : X × Y ⟶ X := π₁
/-- An alternative version of `π₂` if type-class inference fails -/
def π₂' {X Y : C} {H : has_binary_products C} : X × Y ⟶ Y := π₂

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

def diag [H : has_binary_products C] {B : C} : B ⟶ B × B :=
map_to_product.mk (𝟙 B) (𝟙 B)

protected def map {H : has_binary_products C} {A A' B B' : C} (f : A ⟶ A') (g : B ⟶ B') :
  A × B ⟶ A' × B' :=
map_to_product.mk (π₁ ≫ f) (π₂ ≫ g)

local infix ` ×.map `:90 := binary_product.map

protected def iso {H : has_binary_products C} {A A' B B' : C} (f : A ≅ A') (g : B ≅ B') :
  A × B ≅ A' × B' :=
{ hom := f.hom ×.map g.hom,
  inv := f.inv ×.map g.inv,
  hom_inv_id' := omitted,
  inv_hom_id' := omitted }

local infix ` ×.iso `:90 := binary_product.iso

def assoc_hom {H : has_binary_products C} {X Y Z : C} : (X × Y) × Z ⟶ X × (Y × Z) :=
by apply map_to_product.mk (π₁ ≫ π₁) (π₂ ×.map (𝟙 Z))

def assoc_inv {H : has_binary_products C} {X Y Z : C} : X × (Y × Z) ⟶ (X × Y) × Z :=
by apply map_to_product.mk (𝟙 X ×.map π₁) (π₂ ≫ π₂)

def product_assoc {H : has_binary_products C} {X Y Z : C} : (X × Y) × Z ≅ X × (Y × Z) :=
{ hom := assoc_hom,
  inv := assoc_inv,
  hom_inv_id' := omitted,
  inv_hom_id' := omitted}

def product_comm {H : has_binary_products C} {X Y : C} : X × Y ≅ Y × X :=
{ hom := map_to_product.mk π₂ π₁,
  inv := map_to_product.mk π₂ π₁,
  hom_inv_id' := omitted,
  inv_hom_id' := omitted}

def product_assoc4 {H : has_binary_products C} {X Y Z W : C} :
  (X × Y) × (Z × W) ≅ (X × Z) × (Y × W) :=
product_assoc ≪≫
iso.refl X ×.iso (product_assoc.symm ≪≫ product_comm ×.iso iso.refl W ≪≫ product_assoc) ≪≫
product_assoc.symm

example :
  commutative_square
         /-unit-/ (𝟙 unit) /- unit  -/
         (𝟙 unit)            (𝟙 unit)
         /-unit-/ (𝟙 unit) /- unit -/
  := by tidy

end binary_product
open binary_product

section terminal_object

local infix ` × `:60 := binary_product

def terminal_object [has_terminal_object C] : C :=
limit (empty.functor C)

notation `term` := terminal_object

def terminal_map [has_terminal_object C] (A : C) : A ⟶ term :=
is_limit.lift (limit.is_limit (empty.functor C)) (empty_cone A)

lemma terminal_map_eq [has_terminal_object C] {A : C} (f g : A ⟶ term) : f = g :=
omitted

lemma mul_one [has_terminal_object C] [has_binary_products C] (G : C) :
  nonempty $ term × G ≅ G := omitted

lemma one_mul [has_terminal_object C] [has_binary_products C] (G : C) :
  nonempty $ G × term ≅ G := omitted

def mul_one_inv [has_terminal_object C] [has_binary_products C] {G : C} : G ⟶ G × term :=
by apply map_to_product.mk (𝟙 _) (terminal_map G)

def one_mul_inv [has_terminal_object C] [has_binary_products C] {G : C} : G ⟶ term × G :=
by apply map_to_product.mk (terminal_map G) (𝟙 _)

end terminal_object

section pow

local infix ` × `:60 := binary_product

/-- The n-fold product of an object with itself -/
def category.pow [has_binary_products C] [has_terminal_object C] (X : C) : ℕ → C
| 0     := term
| 1     := X
| (n+2) := X × category.pow (n+1)

end pow

namespace finite_limits
open binary_product

instance fintype_two : fintype two :=
{elems := { val := ⟦[two.left, two.right]⟧,
  nodup := by tidy },
  complete := λ x, by cases x; tidy}

example : fintype pempty := by apply_instance

section finite_products

variable (C)
@[class]def has_finite_products := Π α : Type*, fintype α → has_limits_of_shape.{v} (discrete α) C

@[class]def has_equalizers := has_limits_of_shape.{v} (walking_pair) C

@[instance] def has_binary_products_of_has_finite_products [H : has_finite_products C] :
  has_binary_products C := H _ infer_instance

@[instance] def has_terminal_object_of_has_finite_products [H : has_finite_products C] :
  has_limits_of_shape.{v} (discrete pempty) C := H _ infer_instance

@[class]def has_finite_limits := @has_finite_products C 𝒞 × @has_equalizers C 𝒞

end finite_products

end finite_limits

end category_theory.limits
