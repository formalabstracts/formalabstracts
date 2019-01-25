import tactic.tidy

universes u v w

inductive dvector (α : Type u) : ℕ → Type u
| nil {} : dvector 0
| cons : ∀{n} (x : α) (xs : dvector n), dvector (n+1)

@[derive decidable_eq]inductive dfin : ℕ → Type
| fz {n} : dfin (n+1)
| fs {n} : dfin n → dfin (n+1)

namespace dfin
@[simp] def to_nat : ∀ {n}, dfin n → ℕ
| _ fz := 0
| _ (fs n) := n.to_nat + 1

theorem to_nat_lt : ∀ {n} (x : dfin n), x.to_nat < n
| _ fz := nat.succ_pos _
| _ (fs n) := nat.succ_lt_succ (to_nat_lt n)

def to_fin : ∀ {n}, dfin n → fin n
| 0 x := by {cases x}
| (n+1) x := ⟨to_nat x, by apply to_nat_lt⟩

@[extensionality] theorem to_nat_inj {n} {x y : dfin n} (e : x.to_nat = y.to_nat) : x = y :=
by induction x; cases y; injection e with e; [refl, rw x_ih e]

def raise : ∀ {n}, dfin n → dfin (n+1)
| _ fz := fz
| _ (fs n) := fs n.raise

def elim0 {α : Sort*} : dfin 0 → α.

def cast_le : ∀ {m n}, n ≤ m → dfin n → dfin m
| 0 n h x := false.elim (by cases h; cases x)
| (m+1) _ _ fz := fz
| (m+1) _ h (@fs n s) :=
  fs (s.cast_le (nat.le_of_succ_le_succ h))

@[simp] theorem cast_le_to_nat : ∀ {m n}
  (h : n ≤ m) (x : dfin n), (x.cast_le h).to_nat = x.to_nat
| 0 n h x := false.elim (by cases h; cases x)
| (m+1) _ _ fz := rfl
| (m+1) _ h (@fs n s) :=
  congr_arg (+1) (cast_le_to_nat _ _)

theorem cast_le_rfl {n} (x : dfin n) : x.cast_le (le_refl _) = x :=
to_nat_inj (by simp)

def last : ∀ n, dfin (n+1)
| 0 := fz
| (n+1) := fs (last n)

def of_nat : ∀ n, ℕ → option (dfin n)
| 0 m := none
| (n+1) 0 := some fz
| (n+1) (m+1) := fs <$> of_nat n m

def of_nat_lt : ∀ {n} m, m < n → dfin n
| 0 m h := (nat.not_lt_zero _ h).elim
| (n+1) 0 _ := fz
| (n+1) (m+1) h := fs (of_nat_lt m (nat.lt_of_succ_lt_succ h))

@[simp] theorem of_nat_lt_to_nat : ∀ {n m} (h : m < n),
  (of_nat_lt m h).to_nat = m
| 0 m h := (nat.not_lt_zero _ h).elim
| (n+1) 0 _ := rfl
| (n+1) (m+1) h := congr_arg (+1)
  (of_nat_lt_to_nat (nat.lt_of_succ_lt_succ h))

def of_fin : ∀{n}, fin n → dfin n
| n ⟨val, h⟩ := of_nat_lt val h

meta instance reflect : ∀ n, has_reflect (dfin n)
| _ fz := `(fz)
| _ (fs n) := `(fs).subst (reflect _ n)

end dfin

meta def tactic.interactive.to_dfin (m : ℕ) : tactic unit := do
  n ← do {
    `(dfin %%n) ← tactic.target | return (m+1),
    tactic.eval_expr ℕ n },
  m ← dfin.of_nat n m,
  tactic.exact (reflect m)

namespace dfin

instance has_zero_dfin {n} : has_zero $ dfin (n+1) := ⟨fz⟩

instance has_one_dfin : ∀ {n}, has_one (dfin (nat.succ n))
| 0 := ⟨fz⟩
| (n+1) := ⟨fs fz⟩

instance has_add_dfin {n} : has_add (dfin(n)) :=
  ⟨λ x y, of_fin $ (to_fin x) + (to_fin y)⟩

def max : ∀{n}, dfin n → dfin n → dfin n
  | 0 x y                 := by cases x
  | (n+1) (fz) y          := y
  | (n+1) x (fz)          := x
  | (n+1) (fs k₁) (fs k₂) := fs $ max k₁ k₂

end dfin

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

namespace dvector
variables {α : Type u} {β : Type v} {γ : Type w} {n : ℕ}

@[simp] protected def zero_eq : ∀(xs : dvector α 0), xs = []
| [] := rfl

@[simp] protected def concat : ∀{n : ℕ} (xs : dvector α n) (x : α), dvector α (n+1)
| _ []      x' := [x']
| _ (x::xs) x' := x::concat xs x'

@[simp] protected def nth : ∀{n : ℕ} (xs : dvector α n) (m : ℕ) (h : m < n), α
| _ []      m     h := by exfalso; exact nat.not_lt_zero m h
| _ (x::xs) 0     h := x
| _ (x::xs) (m+1) h := nth xs m (lt_of_add_lt_add_right h)

@[reducible, simp] protected def last {n : ℕ} (xs : dvector α (n+1)) : α :=
  xs.nth n (by {repeat{constructor}})

protected def nth' {n : ℕ} (xs : dvector α n) (m : fin n) : α :=
xs.nth m.1 m.2

protected def nth'' : ∀ {n : ℕ} (xs : dvector α n) (m : dfin n), α
| _ (x::xs) dfin.fz       := x
| _ (x::xs) (dfin.fs (m)) := nth'' xs m

protected def mem : ∀{n : ℕ} (x : α) (xs : dvector α n), Prop
| _ x []       := false
| _ x (x'::xs) := x = x' ∨ mem x xs
instance {n : ℕ} : has_mem α (dvector α n) := ⟨dvector.mem⟩

protected def pmem : ∀{n : ℕ} (x : α) (xs : dvector α n), Type
| _ x []       := empty
| _ x (x'::xs) := psum (x = x') (pmem x xs)

protected def mem_of_pmem : ∀{n : ℕ} {x : α} {xs : dvector α n} (hx : xs.pmem x), x ∈ xs
| _ x []       hx := by cases hx
| _ x (x'::xs) hx := by cases hx;[exact or.inl hx, exact or.inr (mem_of_pmem hx)]

@[simp] protected def map (f : α → β) : ∀{n : ℕ}, dvector α n → dvector β n
| _ []      := []
| _ (x::xs) := f x :: map xs

@[simp] protected lemma map_id : ∀{n : ℕ} (xs : dvector α n), xs.map (λx, x) = xs
| _ []      := rfl
| _ (x::xs) := by dsimp; simp*

@[simp] protected lemma map_congr_pmem {f g : α → β} : 
  ∀{n : ℕ} {xs : dvector α n} (h : ∀x, xs.pmem x → f x = g x), xs.map f = xs.map g
| _ []      h := rfl
| _ (x::xs) h :=
  begin
    dsimp, congr' 1, exact h x (psum.inl rfl), apply map_congr_pmem, 
    intros x hx, apply h, right, exact hx
  end

@[simp] protected lemma map_congr_mem {f g : α → β} {n : ℕ} {xs : dvector α n} 
  (h : ∀x, x ∈ xs → f x = g x) : xs.map f = xs.map g :=
dvector.map_congr_pmem $ λx hx, h x $ dvector.mem_of_pmem hx 

@[simp] protected lemma map_congr {f g : α → β} (h : ∀x, f x = g x) : 
  ∀{n : ℕ} (xs : dvector α n), xs.map f = xs.map g
| _ []      := rfl
| _ (x::xs) := by dsimp; simp*

@[simp] protected lemma map_map (g : β → γ) (f : α → β): ∀{n : ℕ} (xs : dvector α n), 
  (xs.map f).map g = xs.map (λx, g (f x))
  | _ []      := rfl
  | _ (x::xs) := by dsimp; simp*

protected lemma map_inj {f : α → β} (hf : ∀{{x x'}}, f x = f x' → x = x') {n : ℕ} 
  {xs xs' : dvector α n} (h : xs.map f = xs'.map f) : xs = xs' :=
begin
  induction xs; cases xs', refl, simp at h, congr;[apply hf, apply xs_ih]; simp [h]
end

@[simp] protected lemma map_concat (f : α → β) : ∀{n : ℕ} (xs : dvector α n) (x : α),
  (xs.concat x).map f = (xs.map f).concat (f x)
| _ []      x' := by refl
| _ (x::xs) x' := by dsimp; congr' 1; exact map_concat xs x'

@[simp] protected lemma map_nth (f : α → β) : ∀{n : ℕ} (xs : dvector α n) (m : ℕ) (h : m < n),
  (xs.map f).nth m h = f (xs.nth m h)
| _ []      m     h := by exfalso; exact nat.not_lt_zero m h
| _ (x::xs) 0     h := by refl
| _ (x::xs) (m+1) h := by exact map_nth xs m _

protected lemma concat_nth : ∀{n : ℕ} (xs : dvector α n) (x : α) (m : ℕ) (h' : m < n+1) 
  (h : m < n), (xs.concat x).nth m h' = xs.nth m h
| _ []      x' m     h' h := by exfalso; exact nat.not_lt_zero m h
| _ (x::xs) x' 0     h' h := by refl
| _ (x::xs) x' (m+1) h' h := by dsimp; exact concat_nth xs x' m _ _

@[simp] protected lemma concat_nth_last : ∀{n : ℕ} (xs : dvector α n) (x : α) (h : n < n+1), 
  (xs.concat x).nth n h = x
| _ []      x' h := by refl
| _ (x::xs) x' h := by dsimp; exact concat_nth_last xs x' _

@[simp] protected lemma concat_nth_last' : ∀{n : ℕ} (xs : dvector α n) (x : α) (h : n < n+1), 
  (xs.concat x).last = x
:= by apply dvector.concat_nth_last

@[simp] protected def append : ∀{n m : ℕ} (xs : dvector α n) (xs' : dvector α m), dvector α (m+n)
| _ _ []       xs := xs
| _ _ (x'::xs) xs' := x'::append xs xs'

@[simp]protected def insert : ∀{n : ℕ} (x : α) (k : ℕ) (xs : dvector α n), dvector α (n+1)
| n x 0 xs := (x::xs)
| 0 x k xs := (x::xs)
| (n+1) x (k+1) (y::ys) := (y::insert x k ys)

@[simp] protected lemma insert_at_zero : ∀{n : ℕ} (x : α) (xs : dvector α n), dvector.insert x 0 xs = (x::xs) := by {intros, induction n; refl} -- why doesn't {intros, refl} work?

@[simp] protected lemma insert_nth : ∀{n : ℕ} (x : α) (k : ℕ) (xs : dvector α n) (h : k < n+1), (dvector.insert x k xs).nth k h = x
| 0 x k xs h := by {cases h, refl, exfalso, apply nat.not_lt_zero, exact h_a}
| n x 0 xs h := by {induction n, refl, simp*}
| (n+1) x (k+1) (y::ys) h := by simp*

protected lemma insert_cons {n k} {x y : α} {v : dvector α n} : (x::(v.insert y k)) = (x::v).insert y (k+1) :=
by {induction v, refl, simp*}

/- Given a proof that n ≤ m, return the nth initial segment of -/
@[simp]protected def trunc : ∀ (n) {m : ℕ} (h : n ≤ m) (xs : dvector α m), dvector α n
| 0 0 _ xs := []
| 0 (m+1) _ xs := []
| (n+1) 0 _ xs := by {exfalso, cases _x}
| (n+1) (m+1) h (x::xs) := (x::@trunc n m (by simp at h; exact h) xs)

@[simp]protected lemma trunc_n_n {n : ℕ} {h : n ≤ n} {v : dvector α n} : dvector.trunc n h v = v :=
  by {induction v, refl, solve_by_elim}

@[simp]protected lemma trunc_0_n {n : ℕ} {h : 0 ≤ n} {v : dvector α n} : dvector.trunc 0 h v = [] :=
  by {induction v, refl, simp}

@[simp]protected lemma trunc_nth {n m l: ℕ} {h : n ≤ m} {h' : l < n} {v : dvector α m} : (v.trunc n h).nth l h' = v.nth l (lt_of_lt_of_le h' h) :=
begin
  induction m generalizing n l, have : n = 0, by cases h; simp, subst this, cases h',
  cases n; cases l, {cases h'}, {cases h'}, {cases v, refl},
  cases v, simp only [m_ih, dvector.nth, dvector.trunc]
end

protected lemma nth_irrel1 : ∀{n k : ℕ} {h : k < n + 1} {h' : k < n + 1 + 1} (v : dvector α (n+1)) (x : α),
  (x :: (v.trunc n (nat.le_succ n))).nth k h = (x::v).nth k h' :=
by {intros, apply @dvector.trunc_nth _ _ _ _ (by {simp, exact dec_trivial}) h (x::v)}

protected def cast {n m} (p : n = m) : dvector α n → dvector α m :=
  by subst p; exact id

@[simp] protected lemma cast_irrel {n m} {p p' : n = m} {v : dvector α n} : v.cast p = v.cast p' := by refl

@[simp] protected lemma cast_rfl {n m} {p : n = m} {q : m = n} {v : dvector α n} : (v.cast p).cast q = v := by {subst p, refl}

protected lemma cast_hrfl {n m} {p : n = m} {v : dvector α n} : v.cast p == v :=
  by subst p; refl

@[simp] protected lemma cast_trans {n m o} {p : n = m} {q : m = o} {v : dvector α n} : (v.cast p).cast q = v.cast (trans p q) := by subst p; subst q; refl

@[simp] protected def remove_mth : ∀ {n : ℕ} (m : ℕ) (xs : dvector α (n+1)) , dvector α (n)
  | 0 _ _  := dvector.nil
  | n 0 (dvector.cons y ys) := ys
  | (n+1) (k+1) (dvector.cons y ys) := dvector.cons y (remove_mth k ys)

 
end dvector
