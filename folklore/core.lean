/- Thomas Hales
Start over, using bundled structures.
Feb 3, 2018
-/

prelude

--basic core stuff

/- The default behavior for Type is Type u, 
for an arbitrary type variable u
(unlike Official-Lean). 
The intention is for universe variables to be mostly
handled behind the scenes. -/


notation `Prop` := Sort 0
notation f ` $ `:1 a:0 := f a

inductive true : Prop
| intro : true

inductive false : Prop

inductive empty : Type

def not (a : Prop) := a → false
prefix `(¬) := not

@[reducible] def ne {α : Sort} (a b : α) := ¬(a = b)
notation a ≠ b := ne a b

inductive eq {α : Sort} (a : α) : α → Prop
| refl : eq a

infix ` = `:50 := eq

structure prod (α : Type) (β : Type) :=
(fst : α) 
(snd : β)

structure and (a b : Prop) : Prop :=
(left : a) 
(right : b)

inductive sum (α : Type) (β : Type)
| inl {} (val : α) : sum
| inr {} (val : β) : sum

inductive or (a b : Prop) : Prop
| inl {} (h : a) : or
| inr {} (h : b) : or

structure sigma {α : Type} (β : α → Type) :=
(fst : α) 
(snd : β fst)

inductive bool : Type
| ff : bool
| tt : bool

structure subtype {α : Sort} (p : α → Prop) :=
(val : α) (property : p val)

inductive option (α : Type)
| none {} : option
| some (val : α) : option

inductive list (T : Type)
| nil {} : list
| cons (hd : T) (tl : list) : list

notation h :: t  := list.cons h t
notation `[` l:(foldr `, ` (h t, list.cons h t) list.nil `]`) := l

inductive nat
| zero : nat
| succ (n : nat) : nat

structure unification_constraint :=
{α : Type} (lhs : α) (rhs : α)

infix ` ≟ `:50   := unification_constraint.mk
infix ` =?= `:50 := unification_constraint.mk

structure unification_hint :=
(pattern : unification_constraint)
(constraints : list unification_constraint)

-- basic set notation.

class_infix `has_mem.mem `(∈)
class_infix `has_sub.sub `(-)
class_infix `has_div.div `(/)
class_infix `has_dvd.dvd `(∣)
class_infix `has_mod.mod `(%)
class_infix `has_le.le `(<=)
class_infix `has_le.le `(≤)
class_infix `has_lt.lt `(<)
class_infix `has_append.append `(++)
class_infix `has_andthen `(;)
class_field `has_emptyc.emptyc `(∅)
class_infix `has_union.union `(∪)
class_infix `has_inter.inter `(∩)
class_infix `has_subset.subset `(⊆)
class_infix `has_ssubset.ssubset `(⊂)
class_infix `has_sdiff.sdiff `(\)
class_infix `has_equiv.equiv `(≈)

/-
Here we tie α to the carrier type.
But we might want to include into differently named carriers.

class something :=
(β : Type)
(has_sub (α = β))
-/
class has_sub  :=    (α : Type) ((-) : α → α → α)
class has_div  :=    (α : Type) ((/) : α → α → α)
class has_dvd  :=    (α : Type) ((|) : α → α → Prop)
class has_mod  :=   (α : Type) ((%) : α → α → α)
class has_le   :=    (α : Type) ((≤) : α → α → Prop)
class has_lt   :=   (α : Type) ((<) : α → α → Prop)
class has_append :=  (α : Type) ((++) : α → α → α)
class has_andthen := (α : Type) (β : Type) (σ : Type) ((;) : α → β → σ)
class has_union :=   (α : Type) ((∪) : α → α → α)
class has_inter :=   (α : Type) ((∩) : α → α → α)
class has_sdiff  :=  (α : Type) ((\) : α → α → α)
class has_equiv :=  (α : Sort) ((≈) : α → α → Prop)
class has_subset :=  (α : Type) ((⊆) : α → α → Prop)
class has_ssubset := (α : Type) ((⊂) : α → α → Prop)

class has_subset :=
(has_subset)
(has_ssubset)
((⊂) :≡ λ a a', (a ⊆ a' ∧ ¬ (a' ⊆ a)))

/-  polymorphic notation for collections.
   Example: {a, b, c}. -/
class has_emptyc :=  (α : Type) (emptyc : α)

class has_insert :=  (α : Type) (γ : Type) := (insert : α → γ → γ)

class has_mem := (α : Type) (β : Type) ((∈) : α → β → Prop)

notation a ∉ s := ¬ has_mem.mem a s

/- repetition of earlier declaration, adding derived fields 
    Might use += notation.  -/
class has_mem :=
(has_mem)
(has_subset (renaming α → β))
((⊆) :≡ λ b b', ∀ (x : α ), x ∈ b → x ∈ b')

/- Type class used to implement the notation { a ∈ c | p a } -/
class has_sep := (α : Type) (γ : Type) (sep : (α → Prop) → γ → γ)

def set (α : Type) := α → Prop

def set_of {α : Type} (p : α → Prop) : set α := p 

protected def set.mem (a : α) (s : set α) := s a

instance {α} (set α) : has_mem  :=
{α := α, β := set α, (∈) := set.mem}

protected def set.sep (p : α → Prop) (s : set α) : set α :=
{a | a ∈ s ∧ p a}

instance {α} (set α): has_sep  :=
{α := α, γ := set α, set.sep⟩

instance {α} (set α) : has_emptyc :=
⟨set α , (λ a, false) ⟩

def univ : set α := λ a, true

protected def set.insert (a : α) (s : set α) : set α :=
{b | b = a ∨ b ∈ s}

instance {α} (set α) : has_insert :=
⟨set α, set.insert⟩

protected def set.union (s₁ s₂ : set α) : set α :=
{a | a ∈ s₁ ∨ a ∈ s₂}

instance {α} (set α) : set.has_union :=
⟨set α, set.union⟩

protected def set.inter (s₁ s₂ : set α) : set α :=
{a | a ∈ s₁ ∧ a ∈ s₂}

instance {α} (set α) : set.has_inter :=
⟨set α, set.inter⟩

def compl (s : set α) : set α :=
{a | a ∉ s}

instance {α} (set α) : has_neg :=
⟨set α, compl⟩

protected def diff (s t : set α) : set α :=
{a ∈ s | a ∉ t}

instance {α} (set α) : has_sdiff :=
⟨set α, set.diff⟩

def powerset (s : set α) : set (set α) :=
{t | t ⊆ s}
prefix `𝒫`:100 := powerset

@[reducible]
def sUnion (s : set (set α)) : set α := {t | ∃ a ∈ s, t ∈ a}
prefix `⋃₀`:110 := sUnion

def image (f : α → β) (s : set α) : set β :=
{b | ∃ a, a ∈ s ∧ f a = b}


/-
Using 1 as a field name in structures is problematic,
because the natural numbers are used to name the projections:
semigroup.1 is the first field of the semigroup structure.

We need a notational way to distinguish them.  Say
semigroup.(1) (field name) vs. semigroup.1 (first field)

The class_* records the hidden name that is used for the 
field, `mul `one `inv, etc.

Elaboration is expected to replace each ` * ` with the
appropriate instance R.mul, where R has upcast to has_mul

Field must have exact name match, 
and the class must have upcast to has_mul (e.g.)
Special notation does not survive renaming of fields.
-/

class_infixl `has_mul.mul `( * ):70
class_field `has_one.one `( 1 )
class_postfix `has_inv.inv `( ⁻¹ ):70
class_infixl `has_add.add `( + ):70
class_fix `has_zero.zero `( 0 )
class_prefix `has_neg.neg `( - ):70 -- unary
class_infix `has_le.le `( ≤ ):50
class_infix `has_le.lt `( < ):50




/- We might have to choose non-generic names α and β 
for fields because they effectively become global
names for algebraic structure carriers. -/

structure has_mul :=
(α : Type)
( ( * ) : α → α → α )

structure semigroup  :=
(has_mul)
(mul_assoc : ∀ a b c : α, a * b * c = a * (b * c))

structure has_one :=
(α : Type)
( ( 1 ) : α)

structure monoid :=
(semigroup)
(has_one)
(one_mul : ∀ a : α, 1 * a = a) 
(mul_one : ∀ a : α, a * 1 = a)

structure has_inv :=
(α : Type)
( ( ⁻¹ ) : α → α )

structure group :=
(monoid)
(has_inv)
(mul_left_inv : ∀ a : α, a⁻¹ * a = 1)

/-
"abelian" is a mixin for semigroup.
-/

structure abelian := 
(semigroup)
(mul_comm : ∀ (a b : α), a * b = b * a)

-- additive structures

structure has_add :=
(α : Type)
( ( + ) : α → α → α)

structure has_zero :=
(α : Type)
( ( 0 ) : α)

structure has_neg :=
(α : Type)
( ( - ) : α → α)

/-
We must not prove any theorems about add_monoid.
We use the upcast to monoid to use all its theorems.
-/

structure add_monoid := 
(has_add)
(has_zero)
(monoid + abelian 
    (renaming 
    ( * ) -> ( + ), 
    ( 1 ) -> ( 0 ), 
    mul_assoc -> add_assoc,
    one_mul -> zero_add,
    mul_one -> add_zero,
    mul_comm  -> add_comm
    ))

/-
add_group repeats add_monoid renamings, 
but we tolerate repetition, because renaming is infrequent.
-/

structure add_group :=
(has_neg)
(add_monoid)
(group + abelian
    (renaming  
    ( * ) -> ( + ), 
    ( 1 ) -> ( 0 ), 
    mul_assoc -> add_assoc,
    one_mul -> zero_add,
    mul_one -> add_zero,
    mul_comm  -> add_comm
    ( ⁻¹ ) -> ( - )
    (mul_left_inv -> add_left_inv)
    (group -> add_group)
    ))

structure semiring :=
(monoid)
(add_monoid)
(left_distrib : ∀ a b c : α, a * (b + c) = (a * b) + (a * c))
(right_distrib : ∀ a b c : α, (a + b) * c = (a * c) + (b * c))
(zero_mul : ∀ a : α, 0 * a = 0)
(mul_zero : ∀ a : α, a * 0 = 0)

structure commutative :=
(semiring)
(mul_comm : ∀ a b : α, a * b = b * a)

structure ring :=
(semiring)
(add_group)

structure integral_domain :=
(ring + commutative)
(zero_ne_one : 0 ≠ (1:α))
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0)

structure division_ring :=
(ring)
( ( ⁻¹ ) : α → α )
(zero_ne_one : 0 ≠ (1:α))
(mul_inv_cancel : ∀ {a : α}, a ≠ 0 → a * a⁻¹ = 1)
(inv_mul_cancel : ∀ {a : α}, a ≠ 0 → a⁻¹ * a = 1)

/-
qed box ▢ "\sqo" has the facetious meaning "quite easily done".
It marks true statements that are to be filled in by automation or the user.
Internally, it means sorry.
-/

/-
If there are two identical fields, the parser should remove duplicates.
For prop fields, it should keep one that provides a proof, if one exists, and
retain its given position among fields.
-/

structure field :=
(division_ring)
(integral_domain)
(eq_zero_or_eq_zero_of_mul_eq_zero : ∀ a b : α, a * b = 0 → a = 0 ∨ b = 0 := ▢  )

-- modules

class_infixl `scalar ` • `:73 

class has_scalar := 
(scalar : Type)
(car : Type)
( ( • ) : scalar → car → car)

/-
We pull the ring out as a parameter because mathematicians
do when they write "R-module".

α := R.α creates definitional equality.
-/

class module (R : ring) :=
(has_scalar)
(α := R.α) 
(add_group (renaming α -> β ))
(smul_left_distrib  : ∀r (x y : β), r • (x + y) = r • x + r • y)
(smul_right_distrib : ∀r s (x : β), (r + s) • x = r • x + s • x)
(mul_smul           : ∀r s (x : β), (r * s) • x = r • (s • x))
(one_smul           : ∀x : β, (1 : α) • x = x)

/-
We don't need a separate definition of vector_space.
Upcasting occurs to allow us to write module F.
variables (F : field) (V : module F)
-/


/- order structures -/
/-
The symbol :≡ marks a static (immutable) field.
-/

structure has_le :=
(α : Type)
( ( ≤ ) : α → α → Prop)
( ( < ) :≡  λ a b, a ≤ b ∧ ¬ b ≤ a)

structure preorder :=
(has_le)
(le_refl : ∀ a : α, a ≤ a)
(le_trans : ∀ a b c : α, a ≤ b → b ≤ c → a ≤ c)

structure partial_order :=
(preorder)
(le_antisymm : ∀ a b : α, a ≤ b → b ≤ a → a = b)

structure linear_order :=
(partial_order)
(le_total : ∀ a b : α, a ≤ b ∨ b ≤ a)

structure ordered_cancel_add_monoid :=
(add_monoid)
(partial_order)
(add_left_cancel : ∀ a b c : α, a + b = a + c → b = c)
(add_right_cancel : ∀ a b c : α, a + b = c + b → a = c := ▢ )
(add_le_add_left       : ∀ a b : α, a ≤ b → ∀ c : α, c + a ≤ c + b)
(le_of_add_le_add_left : ∀ a b c : α, a + b ≤ a + c → b ≤ c)

structure ordered_add_group := 
(ordered_cancel_add_monoid)
(add_group)
(mul_lt_mul_left : ∀ a b : α, a < b → ∀ c : α, c + a < c + b)

/- No separate definition is necessary for linear_order mixin.
For this to work smoothly, an upcast to target A 
needs to extend automatically to target A + mixins.
-/

/-
structure linear_ordered_add_group := (ordered_add_group + linear_order)
structure linear_ordered_cancel_add_monoid := 
(ordered_cancel_add_monoid + linear_order)
-/

structure ordered_semiring :=
(semiring)
(ordered_cancel_add_monoid)
(mul_le_mul_of_nonneg_left:  ∀ a b c : α, a ≤ b → 0 ≤ c → c * a ≤ c * b)
(mul_le_mul_of_nonneg_right: ∀ a b c : α, a ≤ b → 0 ≤ c → a * c ≤ b * c)
(mul_lt_mul_of_pos_left:     ∀ a b c : α, a < b → 0 < c → c * a < c * b)
(mul_lt_mul_of_pos_right:    ∀ a b c : α, a < b → 0 < c → a * c < b * c)

structure linear_ordered_semiring :=
(ordered_semiring)
(linear_order)
(zero_lt_one : zero < one)

structure ordered_ring :=
(ring)
(ordered_add_group)
(ordered_semiring) -- redundant, but adds it to the hierarchy.
(zero_ne_one : 0 ≠ (1:α))
(mul_nonneg : ∀ a b : α, 0 ≤ a → 0 ≤ b → 0 ≤ a * b)
(mul_pos    : ∀ a b : α, 0 < a → 0 < b → 0 < a * b)
(mul_le_mul_of_nonneg_left:= ▢ )
(mul_le_mul_of_nonneg_right:= ▢ )
(mul_lt_mul_of_pos_left:= ▢ )
(mul_lt_mul_of_pos_right:= ▢ )

class linear_ordered_ring :=
(linear_ordered_semiring)
(ordered_ring)

/-
linear_ordered_comm_ring, is replaced with
linear_ordered_ring + commutative.
-/

class linear_ordered_field :=
(linear_ordered_ring) 
(field)

-- powers

class_infixr `has_pow_nat.pow_nat `pow ` ^ `:70

/-
XX We meed to introduce natural numbers, integers,
and associated notation and operations here.
-/

class has_pow_nat :=
(α : Type)
( ( ^ ) : α → ℕ → α)

class has_pow_int  :=
(α : Type)
(pow_int : α → ℤ  → α)

def monoid.pow (monoid M) (a : M.α) : ℕ → α
| 0     := 1
| (n+1) := a * monoid.pow n

/-
We allow conservative extensions of the class.
In this case we are adding has_pow_nat to the hierarchy.
It also propagates automatically to a field of descendants.


Handling of "this": when inside the class declaration,
"this" becomes an implicit argument, so that 
monoid.pow _ a n becomes monoid.pow a n.
-/

class monoid :=
(monoid)
(has_pow_nat)
( ( ^ ) :≡ λ a n, monoid.pow a n)

/-
-[1+n] is an abbreviation in Official-Lean.
-/
def gpow (a : α) : ℤ → α
| (of_nat n) := a^n
| -[1+n]     := (a^(nat.succ n))⁻¹ 

/-
Lattices 
-/
class_field `has_top.top ` ⊤ `
class_field `has_bot.bot ` ⊥ `
class_infixl `has_inf.inf ` ⊓ `:70
class_infixl `has_sup.sup ` ⊔ `:65

structure has_top :=
(α : Type)
( ( ⊤ ) : α)

structure has_bot :=
(α : Type)
( ( ⊥ ) : α)

structure has_inf :=
(α : Type)
( ( ⊓ ) : α → α → α)

structure has_sup :=
(α : Type)
( ( ⊔ ) : α → α → α)

-- class has_imp (α : Type u) := (imp : α → α → α) /- Better name -/

structure order_top :=
(has_top)
(partial_order)
(le_top : ∀ a : α, a ≤ ⊤)

structure order_bot :=
(has_bot)
(partial_order)
(bot_le : ∀ a : α, ⊥ ≤ a)

structure semilattice_sup :=
(has_sup)
(partial_order)
(le_sup_left : ∀ a b : α, a ≤ a ⊔ b)
(le_sup_right : ∀ a b : α, b ≤ a ⊔ b)
(sup_le : ∀ a b c : α, a ≤ c → b ≤ c → a ⊔ b ≤ c)

structure semilattice_inf :=
(has_inf)
(partial_order)
(inf_le_left : ∀ a b : α, a ⊓ b ≤ a)
(inf_le_right : ∀ a b : α, a ⊓ b ≤ b)
(le_inf : ∀ a b c : α, a ≤ b → a ≤ c → a ≤ b ⊓ c)

structure semilattice_sup_top :=
(order_top)
(semilattice_sup)

structure semilattice_sup_bot :=
(order_bot)
(semilattice_sup)

structure semilattice_inf_top :=
(order_top)
(semilattice_inf)

structure semilattice_inf_bot :=
(order_bot)
(semilattice_inf)

structure lattice :=
(semilattice_sup)
(semilattice_inf)

def galois_connection (A : preorder) (B : preorder) 
(l : A.α → B.α) (u : B.α → A.α) := ∀a b, l a ≤ b ↔ a ≤ u b



