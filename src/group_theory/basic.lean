import tactic.omitted
       group_theory.sylow group_theory.perm.cycles group_theory.free_group
       data.nat.enat data.set.finite
       category_theory.concrete_category category_theory.isomorphism

universes u v
open equiv
open category_theory
noncomputable theory

/-- The type of groups. -/
@[reducible] def Group : Type (u+1) := bundled group

/-- Group + group homomorphisms form a concrete category -/
instance concrete_is_group_hom : concrete_category @is_group_hom :=
⟨by introsI α ia; apply_instance, by introsI α β γ ia ib ic f g hf hg; apply_instance⟩

namespace Group
/-- The order of a finite group is defined as its cardinality  -/
noncomputable def order (G : Group) (h : is_finite G) : ℕ :=
classical.take_arbitrary (λ h' : fintype G, @fintype.card G h') h
 (λ h₁ h₂, @fintype.card_congr _ _ h₁ h₂ $ equiv.refl _)

@[priority 2000] instance (G : Group) : group G := G.str
end Group

/-- Transferring the structure of a group along an equivalence of types -/
def group.equiv {α β} (e : α ≃ β) [group α] : group β :=
begin
  refine {mul := λ x y, e (e.symm x * e.symm y), one := e 1, inv := λ x, e (e.symm x)⁻¹, ..},
  omit_proofs
end

/-- The group structure on the universe lift of a type -/
instance ulift.group {α} [group α] : group (ulift α) :=
group.equiv (by tidy : ulift α ≃ α).symm

/-- The universe lift of a group -/
def glift (G : Group.{u}) : Group.{max u v} :=
⟨ulift G, by apply_instance⟩

/-- This is the notion of isomorphic groups which might live in arbitrary universe levels -/
def isomorphic (G : Group.{u}) (H : Group.{v}) : Prop :=
nonempty (glift.{u v} G ≅ glift.{v u} H)

/-- The cyclic of order n -/
def cyclic_group (n : ℕ+) : Group := mk_ob $ multiplicative $ zmod n

/- The alternating groups -/
section
variables {α : Type u} [decidable_eq α] [fintype α]

instance : is_subgroup {g : perm α | g.sign = 1 } := omitted

def alternating_group (n : ℕ) : Group := mk_ob {g : perm (fin n) | g.sign = 1}
end

/- Given N ⊆ G normal, return the canonical surjection G → G/N -/
def canonical_surjection {G : Type*} [group G]  (N : set G) [normal_subgroup N] :
  G → quotient_group.quotient N :=
quotient_group.mk

instance {G : Type*} [group G]  (N : set G) [normal_subgroup N] :
  is_group_hom $ canonical_surjection N :=
omitted

/-- the "extended" group power, where g^∞ is defined as 1 -/
noncomputable def egpow {α : Type*} [group α] (x : α) (n : enat) : α :=
match n.classical_to_option with
| some n := x ^ n
| none   := 1
end

noncomputable instance {α : Type*} [group α] : has_pow α enat := ⟨egpow⟩

variables {α : Type u} [group α] {s : set α} {x y : α}
/-- The centralizer of a set s consists of all elements commuting with all elements of s -/
def centralizer (s : set α) : set α := { g | ∀x ∈ s, g * x = x * g }

instance (s : set α) : is_subgroup (centralizer s) := omitted

-- the normalizer is already defined in mathlib
export is_subgroup (normalizer)

/-- the induced_subgroup t s is the set t viewed as a subgroup s.
  in applications we will have t ⊆ s, but otherwise this definition gives t ∩ s -/
def induced_subgroup (t s : set α) : set s :=
subtype.val ⁻¹' t

instance (t s : set α) [is_subgroup s] [is_subgroup t] : is_subgroup (induced_subgroup t s) :=
is_group_hom.preimage _ _

/-- the subgroup spanned by x is normal in its centralizer -/
instance closure_normal_in_centralizer (x : α) :
  normal_subgroup $ induced_subgroup (group.closure {x}) (centralizer {x} : set α) :=
omitted

/-- A subgroup is normal in its normalizer -/
instance (s : set α) [is_subgroup s] : normal_subgroup (induced_subgroup s (normalizer s)) :=
by { dsimp [induced_subgroup], apply_instance }

/- Primary groups or p-groups -/

def is_primary (p : nat) (α : Type*) [group α] [decidable_eq α] [fintype α] : Prop :=
∀(x : α), ∃(n : ℕ), order_of x = p ^ n

def is_Sylow_subgroup [fintype α] (p : nat) (s : set α) : Prop :=
by { haveI := classical.prop_decidable, exact
  ∃(hs : is_subgroup s), is_primary p s ∧
    (∀ t (ht : is_subgroup t), by { exact is_primary p t } → s ⊆ t → s = t) }

/-- the multiplication is commutative on a subset -/
def commutative_on (s : set α) : Prop := ∀(x y ∈ s), x * y = y * x

/- Conjugacy Classes -/

variable (α)
def right_conjugation {α : Type*} [group α] (x y : α) := y⁻¹ * x * y

/-- A conjugacy class is a set of the form { h * g * h⁻¹ | h : α} for some element g : α -/
def is_conjugacy_class : set (set α) := {s | ∃g, s = set.range (λh, h * g * h⁻¹) }
variable {α}

/-- Every conjugacy class is nonempty -/
lemma is_conjugacy_class.nonempty (s : is_conjugacy_class α) : nonempty s.1 :=
let ⟨g, hg⟩ := s.2 in ⟨⟨g, by { rw [hg], exact ⟨1, by simp⟩ }⟩⟩

/-- Elements in the same conjugacy class have equal order -/
lemma order_irrel_in_conjugacy_class [fintype α] [decidable_eq α] (s : is_conjugacy_class α)
  (h₁ : x ∈ s.1) (h₂ : y ∈ s.1) : order_of x = order_of y :=
omitted

/-- The order of any element in the conjugacy class -/
noncomputable def order_in [fintype α] [decidable_eq α] (s : is_conjugacy_class α) : ℕ :=
classical.take_arbitrary_in s.1 order_of
  (is_conjugacy_class.nonempty s)
  (λ x y, order_irrel_in_conjugacy_class s)

/-- A conjugacy class of a finite group is finite -/
noncomputable instance [fintype α] [decidable_eq α] : fintype (is_conjugacy_class α) :=
@subtype.fintype _ _ _ (classical.dec_pred _)

variable (α)
/-- The set of conjugacy classes where the elements have a given order -/
def is_conjugacy_class_of_order [fintype α] [decidable_eq α] (N : ℕ) : set (is_conjugacy_class α) :=
{ s | order_in s = N }

/-- The set of all conjugacy classes with a given order is finite -/
noncomputable instance [fintype α] [decidable_eq α] (N : ℕ) :
  fintype (is_conjugacy_class_of_order α N) :=
@subtype.fintype _ _ _ (classical.dec_pred _)

/- A list of conjugacy classes with elements of the given order, sorted by ascending cardinality -/
def list_conjugacy_class_of_order [fintype α] [decidable_eq α] (N : ℕ)
  (h : function.injective (λ s : is_conjugacy_class_of_order α N, s.1.1.cardinality)) :
  list (is_conjugacy_class_of_order α N) :=
let f : is_conjugacy_class_of_order α N → ℕ := λ s, s.1.1.cardinality in
let r := pullback_rel f (≤) in
by { haveI : is_antisymm _ r := pullback_rel.is_antisymm f (≤) h,
     exact finset.sort r (@finset.univ (is_conjugacy_class_of_order α N) _) }

def number_of_conjugacy_classes_of_order [fintype α] [decidable_eq α] (N : ℕ) : ℕ :=
fintype.card (is_conjugacy_class_of_order α N)

lemma number_of_conjugacy_classes_of_order_eq [fintype α] [decidable_eq α] (N : ℕ)
  (h : function.injective (λ s : is_conjugacy_class_of_order α N, s.1.1.cardinality)) :
  number_of_conjugacy_classes_of_order α N = (list_conjugacy_class_of_order α N h).length :=
let f : is_conjugacy_class_of_order α N → ℕ := λ s, s.1.1.cardinality in
let r := pullback_rel f (≤) in
begin
  haveI : is_antisymm _ r := pullback_rel.is_antisymm f (≤) h,
  dsimp [number_of_conjugacy_classes_of_order, list_conjugacy_class_of_order],
  omitted --rw [finset.sort_length]
end

/- The m-th conjugacy class of order N -/
def conjugacy_class_classification (G : Group) [fintype G] [decidable_eq G] (N : ℕ) (m : ℕ)
  (h1 : function.injective (λ s : is_conjugacy_class_of_order G N, s.1.1.cardinality))
  (h2 : m < number_of_conjugacy_classes_of_order G N) :
  is_conjugacy_class_of_order G N :=
(list_conjugacy_class_of_order G N h1).nth_le m (by rwa ←number_of_conjugacy_classes_of_order_eq)

namespace char
protected def to_nat_m65 (c : char) : ℕ := c.val - 65
end char

/- The notation for conjugacy classes. The conjugacy class 7C in group G can be written as
conj_class G 7 'C'.
Beware: when using this notation we assume that the group is finite, there are no two conjugacy
classes of the same cardinality with the given order and that there are sufficiently many conjugacy
classes of that order. -/
notation `conj_class` := (λ β N X, @conjugacy_class_classification β (classical.choice omitted)
  (classical.dec_rel _) N (char.to_nat_m65 X) omitted omitted)
