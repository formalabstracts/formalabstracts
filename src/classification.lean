import group_theory

open nat

structure is_cyclic_of_prime_order (G : Group) : Prop :=
(is_cyclic : is_cyclic G)
(is_finite : is_finite G)
(prime_order : prime (G.order is_finite))

def is_simple_alternating_group (G : Group.{0}) : Prop :=
∃n > 4, nonempty (G ≅ alternating_group n)

inductive of_lie_type : Group → Prop
/- todo -/
inductive mathieu_group : Group → Prop
/- todo -/
inductive second_happy_family : Group → Prop
/- todo -/
inductive third_happy_family : Group → Prop
/- todo -/
inductive phariah : Group → Prop
/- todo -/
inductive sporadic_group : Group → Prop
| of_mathieu_group : ∀{{G}}, mathieu_group G → sporadic_group G
| of_second_happy_family : ∀{{G}}, second_happy_family G → sporadic_group G
| of_third_happy_family : ∀{{G}}, third_happy_family G → sporadic_group G
| of_phariah : ∀{{G}}, phariah G → sporadic_group G

-- inductive in_classification_of_finite_simple_groups : Group → Prop
-- | of_lie_type : ∀{{G}}, lie_type G → in_classification_of_finite_simple_groups G
-- | of_sporadic_group : ∀{{G}}, sporadic_group G → in_classification_of_finite_simple_groups G

variable {G : Group.{0}}
theorem classification_of_finite_simple_groups (h₁ : is_finite G) (h₂ : simple_group G) : 
  is_cyclic_of_prime_order G ∨ 
  is_simple_alternating_group G ∨ 
  of_lie_type G ∨ 
  sporadic_group G :=
omitted