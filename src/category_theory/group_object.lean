-- Copyright (c) 2019 Jesse Han. All rights reserved.
-- Released under Apache 2.0 license as described in the file LICENSE.
-- Authors: Jesse Han

import .finite_limits

open category_theory category_theory.limits category_theory.limits.binary_product
     category_theory.limits.finite_limits

universes u v

local infix ` × `:60 := binary_product
local infix ` ×.map `:90 := binary_product.map

structure group_object (C : Type u) [𝓒 : category.{v+1} C] [H : has_binary_products C]
  [H' : has_terminal_object C]  : Type (max u v) :=
(G : C)
(mul : G × G ⟶ G)
(mul_assoc : reassoc_hom G ≫ 𝟙 G ×.map mul ≫ mul = mul ×.map 𝟙 G ≫ mul)
(one : (term : C) ⟶ G)
(one_mul : 𝟙 G = one_mul_inv _ ≫ one ×.map 𝟙 G ≫ mul)
(mul_one : 𝟙 G = mul_one_inv _ ≫ 𝟙 G ×.map one ≫ mul)
(inv : G ⟶ G)
(mul_left_inv : 𝟙 G = map_to_product.mk inv (𝟙 G) ≫ mul)
