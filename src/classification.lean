import .lie_type .sporadic_group 

open nat
local infix ` ≅ `:60 := isomorphic 

/-- Cyclic groups of prime order -/
structure is_cyclic_of_prime_order (G : Group) : Prop :=
(is_cyclic : is_cyclic G)
(is_finite : is_finite G)
(prime_order : prime (G.order is_finite))

/-- The finite simple alternating groups are the even permutations over a finite set with 
more than 4 elements. -/
def is_simple_alternating_group (G : Group) : Prop :=
∃n > 4, G ≅ alternating_group n

/-- The simple groups of Lie type consist of the Chevalley groups, Steinberg groups, Ree groups, Suzuki groups and Tits groups -/
def of_lie_type (G : Group) : Prop :=
chevalley_group G ∨ steinberg_group G ∨ ree_group G ∨ suzuki_group G ∨ tits_group G

/-- The Mathieu groups are the first happy family of sporadic groups -/
def mathieu_group (G : Group) : Prop :=
G ≅ M11 ∨ G ≅ M12 ∨ G ≅ M22 ∨ G ≅ M23 ∨ G ≅ M24

/-- The second happy family of sporadic groups -/
def second_happy_family (G : Group) : Prop :=
G ≅ Co1 ∨ G ≅ Co2 ∨ G ≅ Co3 ∨ G ≅ McL ∨ G ≅ HS ∨ G ≅ J2 ∨ G ≅ Suz

/-- The third happy family of sporadic groups -/
def third_happy_family (G : Group) : Prop :=
G ≅ Monster ∨ G ≅ BabyMonster ∨ G ≅ Fi24' ∨ G ≅ Fi23 ∨ G ≅ Fi22 ∨ G ≅ Th ∨ G ≅ HN ∨ G ≅ He

/-- The pariahs -/
def pariah (G : Group) : Prop :=
G ≅ J1 ∨ G ≅ J3 ∨ G ≅ Ly ∨ G ≅ O'N ∨ G ≅ J4 ∨ G ≅ Ru

/-- The 26 sporadic groups are the finite simple groups which are not of Lie type -/
def sporadic_group (G : Group) : Prop :=
mathieu_group G ∨ second_happy_family G ∨ third_happy_family G ∨ pariah G

/- alternate way of writing this -/
-- inductive sporadic_group (G : Group) : Prop
-- | of_mathieu_group       : mathieu_group G       → sporadic_group
-- | of_second_happy_family : second_happy_family G → sporadic_group
-- | of_third_happy_family  : third_happy_family G  → sporadic_group
-- | of_pariah              : pariah G              → sporadic_group

variable {G : Group}
/-- The classification of finite simple groups: every finite simple group is cyclic, alternating, of Lie type or a sporadic group. -/
theorem classification_of_finite_simple_groups (h₁ : is_finite G) (h₂ : simple_group G) : 
  is_cyclic_of_prime_order G ∨ 
  is_simple_alternating_group G ∨ 
  of_lie_type G ∨ 
  sporadic_group G :=
omitted
