-- Copyright (c) 2019 Jesse Han. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jesse Han

import category_theory.limits.shapes.binary_products
       category_theory.limits.shapes.equalizers
       category_theory.limits.limits

open category_theory.limits.binary_product category_theory.limits category_theory

open category_theory.limits

universes u v

instance fintype_two : fintype two :=
{elems := { val := ⟦[two.left, two.right]⟧,
  nodup := by tidy },
  complete := λ x, by cases x; tidy}

example : fintype pempty := by apply_instance

variables (C : Type u) [𝒞 : category.{v u} C]
include 𝒞 

@[class]def has_finite_products := ∀ α : Type*, (nonempty (fintype α)) → has_limits_of_shape (discrete α) C

@[class]def has_equalizers := has_limits_of_shape (walking_pair) C

def has_binary_products_of_has_finite_products [H : has_finite_products C] :
  has_limits_of_shape (discrete two) C := H _ ⟨by apply_instance⟩
                                -- fails without the instance declaration above

def has_terminal_object_of_has_finite_products [H : has_finite_products C] :
  has_limits_of_shape (discrete pempty) C := H _ ⟨by apply_instance⟩

@[class]def has_finite_limits := (has_finite_products C) × (has_equalizers C)
