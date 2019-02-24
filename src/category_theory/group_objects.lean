-- Copyright (c) 2019 Jesse Han. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jesse Han

import category_theory.limits.shapes.binary_products

open category_theory.limits.binary_product category_theory.limits category_theory

universes u v

variables {C : Type u} [𝒞 : category.{v u} C]
include 𝒞 

local infix ` × `:60 := binary_product

local infix ` ×.map `:60 := binary_product.map

structure group_object [has_limits C] : Type (max u v) :=
(G : C)
(mul : (G × G) ⟶ G)
(mul_assoc : (reassoc_hom G) ≫ (𝟙 _ ×.map mul) ≫ mul = (mul ×.map (𝟙 _)) ≫ mul)
(one : 1 ⟶ G)
(one_mul : (𝟙 G) = one_mul_inv _ ≫ (one ×.map (𝟙 G)) ≫ mul)
(mul_one : (𝟙 G) = mul_one_inv _ ≫ ((𝟙 G) ×.map one) ≫ mul)
(inv : G ⟶ G)
(mul_left_inv : (𝟙 G) = (map_to_product.mk (inv) (𝟙 G)) ≫ mul ) 
