import .lie_type .sporadic_group 

open nat

structure is_cyclic_of_prime_order (G : Group) : Prop :=
(is_cyclic : is_cyclic G)
(is_finite : is_finite G)
(prime_order : prime (G.order is_finite))

def is_simple_alternating_group (G : Group) : Prop :=
∃n > 4, isomorphic G (alternating_group n)

def of_lie_type (G : Group) : Prop :=
chevalley_group G ∨ steinberg_group G ∨ ree_group G ∨ suzuki_group G ∨ tits_group G

def mathieu_group (G : Group) : Prop :=
isomorphic G M11 ∨ isomorphic G M12 ∨ isomorphic G M22 ∨ isomorphic G M23 ∨ isomorphic G M24

def second_happy_family (G : Group) : Prop :=
isomorphic G Co1 ∨ isomorphic G Co2 ∨ isomorphic G Co3 ∨ 
isomorphic G McL ∨ isomorphic G HS ∨ isomorphic G J2 ∨ isomorphic G Suz

def third_happy_family (G : Group) : Prop :=
isomorphic G Monster ∨ isomorphic G BabyMonster ∨ 
isomorphic G Fi24' ∨ isomorphic G Fi23 ∨ isomorphic G Fi22 ∨ 
isomorphic G Th ∨ isomorphic G HN ∨ isomorphic G He

def pariah (G : Group) : Prop :=
isomorphic G J1 ∨ isomorphic G J3 ∨ isomorphic G Ly ∨ 
isomorphic G O'N ∨ isomorphic G J4 ∨ isomorphic G Ru

def sporadic_group (G : Group) : Prop :=
mathieu_group G ∨ second_happy_family G ∨ third_happy_family G ∨ phariah G

/- alternate way of writing this -/
-- inductive sporadic_group (G : Group) : Prop
-- | of_mathieu_group       : mathieu_group G       → sporadic_group
-- | of_second_happy_family : second_happy_family G → sporadic_group
-- | of_third_happy_family  : third_happy_family G  → sporadic_group
-- | of_pariah             : pariah G             → sporadic_group

variable {G : Group}
theorem classification_of_finite_simple_groups (h₁ : is_finite G) (h₂ : simple_group G) : 
  is_cyclic_of_prime_order G ∨ 
  is_simple_alternating_group G ∨ 
  of_lie_type G ∨ 
  sporadic_group G :=
omitted
