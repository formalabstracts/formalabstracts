-- Copyright (c) 2019 Jesse Han. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jesse Han

import .finite_limits

open category_theory category_theory.limits category_theory.limits.binary_product
     category_theory.limits.finite_limits

universes v u

local infix ` × `:60 := binary_product
local infix ` ×.map `:90 := binary_product.map
local infix ` ×.iso `:90 := binary_product.iso

/-- A group object in a category with finite products is an object `G` equipped with morphisms
  `μ : G × G ⟶ G`, `e : 1 ⟶ G` and `i : G ⟶ G` such that the axioms for a group hold
  (which is expressed in terms of commuting diagrams) -/
structure group_object (C : Type u) [𝓒 : category.{v+1} C] [H : has_binary_products.{v} C]
  [H' : has_terminal_object.{v} C]  : Type (max u v) :=
(obj : C)
(mul : obj × obj ⟶ obj)
(mul_assoc : assoc_hom ≫ 𝟙 obj ×.map mul ≫ mul = mul ×.map 𝟙 obj ≫ mul)
(one : term ⟶ obj)
(one_mul : 𝟙 obj = one_mul_inv ≫ one ×.map 𝟙 obj ≫ mul)
(mul_one : 𝟙 obj = mul_one_inv ≫ 𝟙 obj ×.map one ≫ mul)
(inv : obj ⟶ obj)
(mul_left_inv : terminal_map _ ≫ one = map_to_product.mk inv (𝟙 obj) ≫ mul)

/-- A morphism between group objects is a morphism between the objects that commute with
  multiplication -/
structure group_hom {C : Type u} [category.{v+1} C] [has_binary_products C]
  [has_terminal_object C] (G G' : group_object C) : Type (max u v) :=
(map : G.obj ⟶ G'.obj)
(map_mul : G.mul ≫ map = map ×.map map ≫ G'.mul)

/- An action of a group object on any object in the category -/
structure group_action {C : Type u} [category.{v+1} C] [has_binary_products C]
  [has_terminal_object C] (G : group_object C) (X : C) : Type (max u v) :=
(map : G.obj × X ⟶ X)
(map_one : map_to_product.mk (terminal_map X ≫ G.one) (𝟙 X) ≫ map = 𝟙 X)
(map_mul : G.mul ×.map 𝟙 X ≫ map = assoc_hom ≫ 𝟙 G.obj ×.map map ≫ map)

variables {C : Type u} [𝓒 : category.{v+1} C] [p𝓒 : has_binary_products.{v} C]
  [t𝓒 : has_terminal_object.{v} C] {X Y : C} {G G' G₁ G₂ G₃ H : group_object C}
include 𝓒 p𝓒 t𝓒

namespace group_hom

/-- The identity morphism between group objects -/
def id (G : group_object C) : group_hom G G :=
⟨𝟙 G.obj, omitted⟩

/-- Composition of morphisms between group objects -/
def comp (f : group_hom G₁ G₂) (g : group_hom G₂ G₃) : group_hom G₁ G₃ :=
⟨f.map ≫ g.map, omitted⟩

lemma map_one (f : group_hom G G') : G.one ≫ f.map = G'.one := omitted
lemma map_inv (f : group_hom G G') : G.inv ≫ f.map = f.map ≫ G'.inv := omitted

end group_hom

namespace group_object

/-- The category of group objects -/
instance category : category (group_object C) :=
{ hom := group_hom,
  id := group_hom.id,
  comp := λ X Y Z, group_hom.comp }

/-- The terminal group object -/
def terminal_group : group_object C :=
{ obj := term,
  mul := terminal_map _,
  mul_assoc := terminal_map_eq _ _,
  one := terminal_map _,
  one_mul := terminal_map_eq _ _,
  mul_one := terminal_map_eq _ _,
  inv := terminal_map _,
  mul_left_inv := terminal_map_eq _ _ }

/-- The morphism into the terminal group object -/
def hom_terminal_group (G : group_object C) : G ⟶ terminal_group :=
by exact ⟨terminal_map G.obj, omitted⟩

/-- The category of group objects has a terminal object -/
instance has_terminal_object : has_terminal_object (group_object C) :=
has_terminal_object.mk terminal_group hom_terminal_group omitted

/-- The binary product of group objects -/
protected def prod (G G' : group_object C) : group_object C :=
{ obj := G.obj × G'.obj,
  mul := product_assoc4.hom ≫ G.mul ×.map G'.mul,
  mul_assoc := omitted,
  one := map_to_product.mk G.one G'.one,
  one_mul := omitted,
  mul_one := omitted,
  inv := G.inv ×.map G'.inv,
  mul_left_inv := omitted }

protected def pr1 : G.prod G' ⟶ G := by exact ⟨π₁, omitted⟩
protected def pr2 : G.prod G' ⟶ G' := by exact ⟨π₂, omitted⟩
protected def lift (f : H ⟶ G) (g : H ⟶ G') : H ⟶ G.prod G' :=
by exact ⟨map_to_product.mk f.map g.map, omitted⟩

/-- The category of group objects has binary products -/
instance has_binary_products : has_binary_products (group_object C) :=
begin
  apply has_binary_products.mk group_object.prod (λ G G', group_object.pr1)
    (λ G G', group_object.pr2) (λ G G' H, group_object.lift),
  omit_proofs
end

/-- Every group object has a point, i.e. a morphism from the terminal object -/
def one_hom (G : group_object C) : term ⟶ G :=
by exact ⟨G.one, omitted⟩

omit 𝓒 p𝓒 t𝓒
/-- A group object is abelian if multiplication is commutative -/
-- todo: maybe this should be a class
class is_abelian {C : Type u} [𝓒 : category.{v+1} C] [H : has_binary_products.{v} C]
  [H' : has_terminal_object.{v} C] (G : group_object C) : Prop :=
(comm : product_comm.hom ≫ G.mul = G.mul)
include 𝓒 p𝓒 t𝓒

/-- Multiplication is a group homomorphism if `G` is abelian -/
def mul_hom (G : group_object C) [G.is_abelian] : G × G ⟶ G :=
by exact ⟨G.mul, omitted⟩

/-- Inversion is a group homomorphism if `G` is abelian -/
def inv_hom (G : group_object C) [G.is_abelian] : G ⟶ G :=
by exact ⟨G.inv, omitted⟩

instance comm_group_hom (G G' : group_object C) [G'.is_abelian] : comm_group (G ⟶ G') :=
{ mul := λ f g, map_to_product.mk f g ≫ G'.mul_hom,
  mul_assoc := omitted,
  one := terminal_map G ≫ one_hom G',
  one_mul := omitted,
  mul_one := omitted,
  inv := λ f, f ≫ inv_hom G',
  mul_left_inv := omitted,
  mul_comm := omitted }


end group_object
