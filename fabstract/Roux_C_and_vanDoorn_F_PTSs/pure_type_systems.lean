open list option
/- Pure Type Systems using DeBruijn indices -/

-- the specification of a PTS
structure pure_type_system : Type 2 :=
  (Sorts : Type)
  (Axioms : Sorts → Sorts → Prop)
  (Relations : Sorts → Sorts → Sorts → Prop)

namespace pure_type_system
section

parameter (PTS : pure_type_system)

/- untyped terms of a PTS -/
inductive term : Type
| var  : ℕ -> term
| sort : PTS.Sorts -> term
| pi   : term -> term -> term
| abs  : term -> term -> term
| app  : term -> term -> term

local notation `#`:max := term.var
local notation `!`:max := term.sort
local notation `Π'` := term.pi
local notation `λ'` := term.abs
local infix `⬝` := term.app

parameter {PTS}

/- lifting of terms -/
def lift_term : term → ℕ → ℕ → term
| (term.var ._ x) n k := if k ≤ x then #(x+n) else #x
| (term.sort s)   n k := !s
| (term.pi A B)   n k := Π' (lift_term A n k) (lift_term B n (k+1))
| (term.abs A b)  n k := λ' (lift_term A n k) (lift_term b n (k+1))
| (term.app a b)  n k := lift_term a n k ⬝ lift_term b n k

local notation t ` ↑ ` n ` # ` k := lift_term t n k
local infix ` ↑ ` := λn k, lift_term n k 0

/- substitution -/
def subst : term → term → ℕ → term
| (term.var ._ x) t n := if n < x then #x else if n = x then t ↑ n else #(x-1)
| (term.sort s)   t n := !s
| (term.pi A B)   t n := Π' (subst A t n) (subst B t (n+1))
| (term.abs A b)  t n := λ' (subst A t n) (subst b t (n+1))
| (term.app a b)  t n := subst a t n ⬝ subst b t n

def context := list term

/- t is the n-th term of Γ, correctly lifted -/
def item_lift (Γ : context) (n : ℕ) (t : term) : Prop :=
∃u, t = u ↑ (n+1) ∧ nth Γ n = some u

/- The contextual closure of single-step beta reduction -/
inductive beta : term → term → Prop
| beta : ∀A t u, beta ((λ' A t) ⬝ u) (subst t u 0)
| pil  : ∀{t t'} u, beta t t' → beta (Π' t u) (Π' t' u)
| pir  : ∀t {u u'}, beta u u' → beta (Π' t u) (Π' t u')
| absl : ∀{t t'} u, beta t t' → beta (λ' t u) (λ' t' u)
| absr : ∀t {u u'}, beta u u' → beta (λ' t u) (λ' t u')
| appl : ∀{t t'} u, beta t t' → beta (t ⬝ u) (t' ⬝ u)
| appr : ∀t {u u'}, beta u u' → beta (t ⬝ u) (t ⬝ u')

local infix ` →β `:50 := beta

/- the transitive closure of beta reduction -/
inductive betas : term → term → Prop
| refl   : ∀t, betas t t
| transl : ∀{a b c}, a →β b → betas b c → betas a c

local infix ` ↠β `:50 := betas

/- The congruence closure of beta reduction -/
inductive betac : term → term → Prop
| of_betas : ∀{t s}, t ↠β s → betac t s
| symm   : ∀{t s}, betac t s → betac s t
| transl : ∀{a b c}, betac a b → betac b c → betac a c

local infix ` ≡β `:50 := betas

/- terms in normal form -/
definition is_normal (t : term) : Prop :=
∀(s : term), ¬(t →β s)

definition has_normal_form (t : term) : Prop :=
∃(s : term), is_normal s ∧ t ↠β s

definition strongly_normalizing_term (t : term) : Prop :=
¬∃(f : ℕ → term), f 0 = t ∧ ∀n, f n →β f (n+1)

/- well formed contexts, well typed terms -/
mutual inductive wf, typ
with wf : context → Prop
| nil : wf nil
| cons : Π{Γ A s}, typ Γ A (!s) → wf (A::Γ)
with typ : context → term → term → Prop
| sort : Π{Γ s t}, PTS.Axioms s t → wf Γ → typ Γ (!s) (!t)
| var  : Π{Γ s x}, wf Γ → item_lift Γ x s → typ Γ (#x) s
| pi   : Π{Γ A B s₁ s₂ u}, PTS.Relations s₁ s₂ u → typ Γ A (!s₁) → typ (A::Γ) B (!s₂) →
         typ Γ (Π' A B) (!u)
| lam  : Π{Γ A B M s₁ s₂ s₃}, PTS.Relations s₁ s₂ s₃ → typ Γ A (!s₁) → typ (A::Γ) B (!s₂) →
         typ (A::Γ) M B → typ Γ (λ' A M) (Π' A B)
| app  : Π{Γ A B t u}, typ Γ t (Π' A B) → typ Γ u A → typ Γ (t ⬝ u) (subst B u 0)
| conv : Π{Γ A B t s}, A ≡β B → typ Γ t A → typ Γ B (!s) → typ Γ t B

local notation Γ ` ⊢ ` t ` : ` T := typ Γ t T
-- where "Γ ⊢ t : T" := (typ Γ t T) : UT_scope.

definition is_well_typed (t : term) : Prop :=
∃(Γ : context) (A : term), typ Γ t A -- Γ ⊢ t : A

parameter (PTS)

/- weakly and strongly normalizing PTSs -/
definition is_weakly_normalizing : Prop :=
∀(t : term), is_well_typed t → has_normal_form t

definition is_strongly_normalizing : Prop :=
∀(t : term), is_well_typed t → strongly_normalizing_term t

end

end pure_type_system
