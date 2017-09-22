
inductive direction | left | right
instance : decidable_eq direction := by tactic.mk_dec_eq_instance

local prefix ^ := option

def nondet_turing_machine (state symbol : Type) [decidable_eq state] [decidable_eq symbol] :=
state → ^symbol → state → ^symbol → direction → bool

def turing_machine (state symbol : Type) [decidable_eq state] [decidable_eq symbol] :=
state → ^symbol → ^(state × ^symbol × direction)

variables {S A : Type} [decidable_eq S] [decidable_eq A]

def to_nondet (TM : turing_machine S A) : nondet_turing_machine S A :=
λ s a s' a' d', (TM s a = some (s', a', d') : bool)

instance : has_coe (turing_machine S A) (nondet_turing_machine S A) :=
⟨to_nondet⟩

structure TM_config (S A : Type) :=
(cur : S)
(head : ^A)
(left : list (^A))
(right : list (^A))

def uncons : list (^A) → ^A × list (^A)
| []       := (none, [])
| (a :: s) := (a, s)

def cons' : ^A → list (^A) → list (^A)
| none [] := []
| v    s  := v::s

def apply_step
  (l r : list (^A)) (c : S) (v : ^A) : direction → TM_config S A
| direction.left  := let ⟨a, l'⟩ := uncons l in ⟨c, a, l', cons' v r⟩
| direction.right := let ⟨a, r'⟩ := uncons r in ⟨c, a, cons' v l, r'⟩

inductive step (TM : nondet_turing_machine S A) :
  TM_config S A → TM_config S A → Prop
| mk {c h l r c' v d} :
  TM c h c' v d → step ⟨c, h, l, r⟩ (apply_step l r c' v d)

def halts (TM) (s : TM_config S A) : Prop := ∀ s', ¬ step TM s s'

inductive computes (TM) (res : TM_config S A) : nat → TM_config S A → Prop
| done : halts TM res → computes 0 res
| step {s s' n} : step TM s s' → computes n s' → computes (n+1) s

def next (TM : turing_machine S A) : TM_config S A → option (TM_config S A)
| ⟨c, h, l, r⟩ := match TM c h with
  | none := none
  | some (c', v, d) := some (apply_step l r c' v d)
  end

theorem next_step {TM : turing_machine S A}
  (s s' : TM_config S A) : next TM s = some s' ↔ @step S A _ _ TM s s' :=
begin
  constructor,
  { cases s, simp [next],
    ginduction TM cur head with e,
    { intro e, injection e },
    { cases a with s' a, cases a with v d,
      simp [next], intro i, injection i with h, subst h,
      exact ⟨to_bool_true e⟩ } },
  { intro h, induction h,
    simp [next],
    conv at a {whnf}, rw of_to_bool_true a,
    refl }
end

theorem next_halts {TM : turing_machine S A}
  (s : TM_config S A) : next TM s = none ↔ @halts S A _ _ TM s :=
begin
  ginduction (next TM s) with e,
  { simp, intros s' h,
    injection e.symm.trans ((next_step _ _).2 h) },
  { constructor; intro h, {contradiction},
    exact absurd ((next_step _ _).1 e) (h _) }
end

inductive tape_alpha (n : nat) : Type
| input {} : bool → tape_alpha
| delim {} : tape_alpha
| work {} : fin n → tape_alpha
instance (n) : decidable_eq (tape_alpha n) := by tactic.mk_dec_eq_instance

def TATM (s n : nat) := turing_machine (fin (s+1)) (tape_alpha n)

def NTATM (s n : nat) := nondet_turing_machine (fin (s+1)) (tape_alpha n)

instance (s n) : has_coe (TATM s n) (NTATM s n) := ⟨to_nondet⟩

def encode {n} : list (list bool) → list (^tape_alpha n)
| [] := []
| ([] :: ls) := some tape_alpha.delim :: encode ls
| ((a::l) :: ls) := some (tape_alpha.input a) :: encode (l::ls)

def computes_fn_in_time {s n} (TM : NTATM s n) {m}
  (f : (fin m → list bool) → list bool)
  (tm : (fin m → list bool) → nat) : Prop :=
∀ i : fin m → list bool,
∃ (n ≤ tm i) e,
  computes TM
    ⟨e, none, [], encode [f i]⟩ n
    ⟨0, none, [], encode (array.to_list ⟨i⟩)⟩
