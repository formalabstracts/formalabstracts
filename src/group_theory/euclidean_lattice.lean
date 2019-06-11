import .basic data.real.basic linear_algebra.basic ..data.dvector linear_algebra.basis

local notation h :: t  := dvector.cons h t
local notation `[` l:(foldr `, ` (h t, dvector.cons h t) dvector.nil `]`) := l

/- In case we have to work with order-theoretic lattices later,
   we'll use the term "Euclidean lattice" -/

/-- A Euclidean lattice of dimension n is a subset of ℝ^n which satisfies the following property: every element is a ℤ-linear combination of a basis for ℝ^n -/

def euclidean_space (n) := dvector ℝ n

instance euclidean_space_add_comm_group {n} : add_comm_group $ euclidean_space n :=
{ add := by {induction n, exact λ x y, [],
             intros x y, cases x, cases y,
             refine (_::(n_ih x_xs y_xs)), exact x_x + y_x},
  add_assoc := λ _ _ _, omitted,
  zero := by {induction n, exact [], exact (0::n_ih)},
  zero_add := λ _, omitted,
  add_zero := λ _, omitted,
  neg := by {induction n, exact λ _, [], intro x, cases x, exact (-x_x :: n_ih x_xs)},
  add_left_neg := λ _, omitted,
  add_comm := omitted}

noncomputable instance euclidean_space_vector_space {n} : vector_space ℝ $ euclidean_space n :=
{ smul := by {induction n, exact λ _ _, [], intros r x, cases x, exact (r * x_x :: n_ih r x_xs)},
  smul_add := omitted,
  add_smul := omitted,
  mul_smul := omitted,
  one_smul := by omitted,
  zero_smul := omitted,
  smul_zero := omitted}

def inner_product : ∀ {n}, euclidean_space n → euclidean_space n → ℝ
| 0 _ _ := 0
| (n+1) (x::xs) (y::ys) := x*y + inner_product xs ys

def is_linear {n} (f : euclidean_space n → ℝ) :=
  (∀ x y, f(x+y) = f x + f y) ∧ ∀ (r : ℝ) x, f(r • x) = r • (f x)

def is_multilinear {n k} (f : dvector (euclidean_space (n)) k → ℝ) : Prop :=
begin
  induction k with k ih, exact ∀ x, f x = 0,
  exact ∀ k' (xs : euclidean_space n) (xss : dvector (euclidean_space n) k),
      is_linear $ λ xs, f $ dvector.insert xs k' xss
end


def is_alternating {n k} (f : dvector (euclidean_space (n)) k → ℝ) :=
  ∀ i j (h₁ : i < k) (h₂ : j < k) (xs : dvector (euclidean_space n) (k)),
    xs.nth i h₁ = xs.nth j h₂ → f xs = 0

/-- The canonical inclusion from ℝ^n → ℝ^(n+1) given by inserting 0 at the end of all vectors -/
def euclidean_space_canonical_inclusion {n} : euclidean_space n → euclidean_space (n+1) :=
  λ xs, by {induction xs, exact [0], exact xs_x :: xs_ih}

def identity_matrix : ∀(n), dvector (euclidean_space n) n
| 0 := []
| (n+1) := ((@identity_matrix n).map (λ xs, euclidean_space_canonical_inclusion xs)).concat $
            (0 : euclidean_space n).concat 1

lemma identity_matrix_1 : identity_matrix 1 = [[1]] := by refl

lemma identity_matrix_2 : identity_matrix 2 = [[1,0],[0,1]] := by refl

def sends_identity_to_1 {n} (f : dvector (euclidean_space (n)) n → ℝ) : Prop :=
  f (identity_matrix _) = 1

/-- The determinant is the unique alternating multilinear function which sends the identity
   matrix to 1-/
def determinant_spec {n} : ∃! (f : dvector (euclidean_space n) n → ℝ),
  is_multilinear f ∧ is_alternating f ∧ sends_identity_to_1 f := omitted

noncomputable def determinant {n} : dvector (euclidean_space n) n → ℝ :=
classical.the _ determinant_spec

local notation `⟪`:90 x `,` y `⟫`:0  := inner_product x y

local notation `ℝ^^`:50 n:0 := euclidean_space n

instance ℤ_module_euclidean_space {n} : module ℤ (ℝ^^n) :=
{ smul := λ z x, by {induction x, exact [], exact z * x_x :: x_ih},
  smul_add := omitted,
  add_smul := omitted,
  mul_smul := omitted,
  one_smul := omitted,
  zero_smul := omitted,
  smul_zero := omitted }

/- An x : ℝ^^n is in the integral span of B if it can be written as a ℤ-linear combination of elements of B -/
def in_integral_span {n} (B : set ℝ^^n) : (ℝ^^n) → Prop :=
 λ x, x ∈ submodule.span ℤ B

def is_euclidean_lattice {n : ℕ} (Λ : set ℝ^^n) := ∃ B : set ℝ^^n, is_basis ℝ B ∧ ∀ x ∈ Λ, in_integral_span B x

def euclidean_lattice (n : ℕ) := {Λ : set (ℝ^^n) // is_euclidean_lattice Λ}

def is_integer : set ℝ := (λ x : ℤ, x) '' set.univ

def is_even_integer : set ℝ := (λ x : ℤ, x) '' (λ z, ∃ w, 2 * w = z)

/-- A Euclidean lattice is even if for every x : Λ, ||x||^2 is an even integer -/
def even {n} (Λ : euclidean_lattice n) : Prop := ∀ x ∈ Λ.val, is_even_integer ⟪x ,x⟫

/-- A Euclidean lattice is unimodular if it has a basis with determinant 1 -/
def unimodular {n} (Λ : euclidean_lattice n) : Prop := ∃ B : (dvector (ℝ^^n) n), is_basis ℝ (B.to_set) ∧ ∀ x ∈ Λ.val, in_integral_span (B.to_set) x ∧ determinant B = 1

def GL (n) := linear_map.general_linear_group ℝ (ℝ^^n)

noncomputable instance GL_monoid (n) : monoid ((ℝ^^n) →ₗ[ℝ] ℝ^^n) :=
{ mul := λ f g, linear_map.comp f g,
  mul_assoc := λ _, omitted,
  one := { to_fun := id,
  add := omitted,
  smul := omitted },
  one_mul := omitted,
  mul_one := omitted}

noncomputable instance GL_mul (n) : has_mul $ GL n := ⟨λ f g, { val := linear_map.comp f.val g.val,
  inv := linear_map.comp f.inv g.inv,
  val_inv := omitted,
  inv_val := omitted}⟩

noncomputable instance GL_inv (n) : has_inv $ GL n :=
⟨by {intro σ, cases σ,
  exact { val := σ_inv,
  inv := σ_val,
  val_inv := σ_inv_val,
  inv_val := σ_val_inv }}⟩

/-- An automorphism of an n-dimensional Euclidean lattice is a map in GL(n) which permutes Λ -/
def is_lattice_automorphism {n} {Λ : euclidean_lattice n} (σ : GL n) : Prop :=
  set.bij_on (λ x : ℝ^^n, by cases σ; exact σ_val.to_fun x : (ℝ^^n) → (ℝ^^n)) Λ.val Λ.val

/- Source: https://groupprops.subwiki.org/wiki/Leech_lattice -/

/-- The Leech lattice is the unique even unimodular lattice Λ_24 in 24 dimensions
such that it has no vectors with norm equal to 4.
It is unique up to isomorphism, so any Λ_24 witnessing this existential assertion will suffice.
-/

def leech_lattice_spec : ∃ Λ : euclidean_lattice 24,
  even Λ ∧ unimodular Λ ∧ ∀ x ∈ Λ.1, ⟪x,x⟫ ≠ 4 := omitted

noncomputable def Λ_24 := classical.some leech_lattice_spec

noncomputable def lattice_Aut {n} (Λ : euclidean_lattice n): Group :=
{ α := {σ // @is_lattice_automorphism _ Λ σ},
  str := { mul := λ f g, ⟨f * g, omitted⟩,
  mul_assoc := omitted,
  one := { val := { val := { to_fun := id,
  add := omitted,
  smul := omitted },
  inv := { to_fun := id,
  add := omitted,
  smul := omitted },
  val_inv := omitted,
  inv_val := omitted },
  property := omitted },
  one_mul := omitted,
  mul_one := omitted,
  inv := λ σ, ⟨σ.val ⁻¹, omitted⟩,
  mul_left_inv := omitted }}
