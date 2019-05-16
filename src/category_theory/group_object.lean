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

structure group_object (C : Type u) [𝓒 : category.{v+1} C] [H : has_binary_products.{v} C]
  [H' : has_terminal_object.{v} C]  : Type (max u v) :=
(obj : C)
(mul : obj × obj ⟶ obj)
(mul_assoc : assoc_hom ≫ 𝟙 obj ×.map mul ≫ mul = mul ×.map 𝟙 obj ≫ mul)
(one : term ⟶ obj)
(one_mul : 𝟙 obj = one_mul_inv ≫ one ×.map 𝟙 obj ≫ mul)
(mul_one : 𝟙 obj = mul_one_inv ≫ 𝟙 obj ×.map one ≫ mul)
(inv : obj ⟶ obj)
(mul_left_inv : 𝟙 obj = map_to_product.mk inv (𝟙 obj) ≫ mul)

structure group_hom {C : Type u} [category.{v+1} C] [has_binary_products C]
  [has_terminal_object C] (G G' : group_object C) : Type (max u v) :=
(map : G.obj ⟶ G'.obj)
(map_mul : G.mul ≫ map = map ×.map map ≫ G'.mul)

variables {C : Type u} [𝓒 : category.{v+1} C] [p𝓒 : has_binary_products.{v} C]
  [t𝓒 : has_terminal_object.{v} C] {X Y : C} {G G' G₁ G₂ G₃ H : group_object C}
include 𝓒 p𝓒 t𝓒

namespace group_hom

def id (G : group_object C) : group_hom G G :=
⟨𝟙 G.obj, omitted⟩

def comp (f : group_hom G₁ G₂) (g : group_hom G₂ G₃) : group_hom G₁ G₃ :=
⟨f.map ≫ g.map, omitted⟩

lemma map_one (f : group_hom G G') : G.one ≫ f.map = G'.one := omitted
lemma map_inv (f : group_hom G G') : G.inv ≫ f.map = f.map ≫ G'.inv := omitted

end group_hom

namespace group_object

instance group_object.category : category (group_object C) :=
{ hom := group_hom,
  id := group_hom.id,
  comp := λ X Y Z, group_hom.comp }

def terminal_group : group_object C :=
{ obj := term,
  mul := terminal_map _,
  mul_assoc := terminal_map_eq _ _,
  one := terminal_map _,
  one_mul := terminal_map_eq _ _,
  mul_one := terminal_map_eq _ _,
  inv := terminal_map _,
  mul_left_inv := terminal_map_eq _ _ }

def hom_terminal_group (G : group_object C) : G ⟶ terminal_group :=
by exact ⟨terminal_map G.obj, omitted⟩

def has_terminal_object : has_terminal_object (group_object C) :=
has_terminal_object.mk terminal_group hom_terminal_group omitted

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

def has_binary_products : has_binary_products (group_object C) :=
begin
  apply has_binary_products.mk group_object.prod (λ G G', group_object.pr1)
    (λ G G', group_object.pr2) (λ G G' H, group_object.lift),
  omit_proofs
end



end group_object
