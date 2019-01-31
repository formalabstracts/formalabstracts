import preliminaries group_theory.sylow group_theory.perm data.zmod.basic
universes u v
open equiv 
open category_theory (mk_ob)
noncomputable theory

/- cyclic groups -/
def cyclic_group (n : ℕ+) : Group := mk_ob $ multiplicative $ zmod n

/- The alternating groups -/
section
variables {α : Type u} [decidable_eq α] [fintype α]

instance : is_subgroup {g : perm α | g.sign = 1 } := omitted

def alternating_group (n : ℕ) : Group := mk_ob {g : perm (fin n) | g.sign = 1}
end

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

-- the normalizer is already defined
export is_subgroup (normalizer)

/-- the induced_subgroup t s is the set t viewed as a subgroup s.
  in applications we will have t ⊆ s, but otherwise this definition gives t ∩ s -/
def induced_subgroup (t s : set α) : set s :=
subtype.val ⁻¹' t

instance (t s : set α) [is_subgroup s] [is_subgroup t] : is_subgroup (induced_subgroup t s) :=
is_group_hom.preimage _ _

/-- the subgroup spanned by x is normal in its centralizer -/
instance (x : α) : 
  normal_subgroup $ induced_subgroup (group.closure {x}) (centralizer {x} : set α) :=
omitted

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
/-- A conjugacy class is a set of the form { h * g * h⁻¹ | h : α} for some element g : α -/
def is_conjugacy_class : set (set α) := {s | ∃g, s = (λh, h * g * h⁻¹) '' set.univ }

variable {α}
/-- Elements in the same conjugacy class have equal order -/
def order_irrel_in_conjugacy_class [fintype α] [decidable_eq α] (s : is_conjugacy_class α) 
  (h₁ : x ∈ s.1) (h₂ : y ∈ s.1) : order_of x = order_of y :=
omitted

/-- The order of any element in the conjugacy class -/
noncomputable def order_in [fintype α] [decidable_eq α] (s : is_conjugacy_class α) : ℕ := 
order_of (classical.some s.2)

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
  exact omitted --rw [finset.sort_length]
end

/- The m-th conjugacy class of order N -/
def conjugacy_class_classification (G : Group) [fintype G] [decidable_eq G] (N : ℕ) (m : ℕ) 
  (h1 : function.injective (λ s : is_conjugacy_class_of_order G N, s.1.1.cardinality))
  (h2 : m < number_of_conjugacy_classes_of_order G N) : 
  is_conjugacy_class_of_order G N :=
(list_conjugacy_class_of_order G N h1).nth_le m (by rwa ←number_of_conjugacy_classes_of_order_eq)

/- The notation for conjugacy classes. The conjugacy class 7C in group G can be written as
conj_class G 7 'C'.
Beware: when using this notation we assume that the group is finite, there are no two conjugacy classes of the same cardinality with the given order and that there are sufficiently many conjugacy classes of that order -/
notation `conj_class` := (λ β N X, @conjugacy_class_classification β (classical.choice omitted) (classical.dec_rel _) N (char.to_nat_m65 X) omitted omitted)
