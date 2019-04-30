import ..basic
       ring_theory.algebra
       linear_algebra.tensor_product
       ring_theory.ideal_operations
       category_theory.concrete_category
open set

universes u v w

/- move to ideal-/
namespace ideal
namespace quotient
variables {α : Type*} {β : Type*} [comm_ring α] [comm_ring β] {S : ideal α} {T : ideal β}
  {f : α → β} {H : ∀ {{a : α}}, a ∈ S → f a ∈ T}

-- replace lift
def lift' (S : ideal α) (f : α → β) [is_add_group_hom f] (H : ∀ (a : α), a ∈ S → f a = 0) :
  quotient S → β :=
λ x, quotient.lift_on' x f $ λ (a b) (h : _ ∈ _),
eq_of_sub_eq_zero (by simpa only [is_add_group_hom.sub f] using H _ h)

def map (S : ideal α) (T : ideal β) (f : α → β) [is_add_group_hom f]
  (H : ∀ {{a : α}}, a ∈ S → f a ∈ T) : quotient S → quotient T :=
begin
  haveI : is_add_group_hom ((mk T : β → quotient T) ∘ f) := is_add_group_hom.comp _ _,
  refine ideal.quotient.lift' S (mk T ∘ f) _,
  intros x hx, refine ideal.quotient.eq.2 _, rw [sub_zero], exact H hx
end

@[simp] lemma map_mk' [is_add_group_hom f] (x : α) : map S T f H (mk S x) = mk T (f x) := rfl

instance map.is_ring_hom [is_ring_hom f] : is_ring_hom (map S T f H) :=
by dsimp [map]; exact omitted

end quotient
end ideal

/- move to module -/

section module

variables {R : Type u} {S : Type*} [ring R]
variables {M : Type*} [add_comm_group M]
variables [module R M]

instance smul.is_add_group_hom {r : R} : is_add_group_hom (λ x : M, r • x) :=
by refine_struct {..}; simp [smul_add]

def quotient_add_group.quotient.module {s : set M} [normal_add_subgroup s]
  (h : ∀(r : R) {x : M}, x ∈ s → r • x ∈ s) : module R (quotient_add_group.quotient s) :=
{ smul := λ r, quotient_add_group.map _ _ (λ(x : M), r • x) (λ x h', h r h'),
  smul_add := omitted,
  add_smul := omitted,
  mul_smul := omitted,
  one_smul := omitted,
  zero_smul := omitted,
  smul_zero := omitted }

end module

variables {R : Type u} {S : Type*} [comm_ring R] [comm_ring S]
variables {M : Type*} {N : Type*} {P : Type*} [ring M] [ring N] [ring P]
variables {A : Type*} {B : Type*} {X : Type*} [comm_ring A] [comm_ring B] [comm_ring X]
variables [algebra R M] [algebra R N] [algebra R P] [algebra R A] [algebra R B] [algebra R X]

notation M ` ⊗[`:100 R `] ` N:100 := tensor_product R M N

namespace algebra

/-- A R-module is an R-algebra if scalar multiplication commutes with multiplication -/
def of_module {R : Type u} {A : Type v} [comm_ring R] [ring A] [m : module R A]
  (h : ∀(r : R) (x y : A), r • x * y = x * r • y) : algebra R A :=
{ to_fun := λ r, r • 1,
  hom := ⟨one_smul R 1, by { intros, rw [h, one_mul, mul_smul] }, λ x y, add_smul x y 1⟩,
  commutes' := by { intros, rw [h, one_mul, ←h, mul_one] },
  smul_def' := by { intros, rw [h, one_mul] },
  ..m }

/-- The codomain of a ring homomorphism viewed as an algebra over the domain -/
def induced_algebra (f : R → S) [is_ring_hom f] : Type* := S
instance (f : R → S) [is_ring_hom f] : comm_ring (induced_algebra f) := _inst_2
instance (f : R → S) [is_ring_hom f] : algebra R (induced_algebra f) :=
algebra.of_ring_hom f (by apply_instance)

end algebra
open algebra
namespace alg_hom

/-- A ring homomorphism induces an algebra homomorphism -/
protected def of_ring_hom (f : R → S) [is_ring_hom f] : R →ₐ[R] induced_algebra f :=
{ to_fun := f,
  hom := by apply_instance,
  commutes' := λ r, rfl }

end alg_hom

open algebra

namespace tensor_product

/- short-ciruiting some type class inference -/
protected def add_comm_group' : add_comm_group (M ⊗[R] N) := by apply_instance
protected def module' : module R (M ⊗[R] N) := by apply_instance
local attribute [instance, priority 2000] tensor_product.add_comm_group' tensor_product.module'
protected def lmap_add_comm_group : add_comm_group (M ⊗[R] N →ₗ[R] M ⊗[R] N) := by apply_instance
protected def lmap_module : module R (M ⊗[R] N →ₗ[R] M ⊗[R] N) := by apply_instance
local attribute [instance, priority 2000]
  tensor_product.lmap_add_comm_group tensor_product.lmap_module

/-- The multiplication on the tensor product of two R-algebras as a bilinear map -/
protected def mul : M ⊗[R] N →ₗ[R] M ⊗[R] N →ₗ[R] M ⊗[R] N :=
begin
  refine tensor_product.lift ⟨λ m, ⟨λ n, _, omitted, omitted⟩, omitted, omitted⟩,
  refine tensor_product.lift ⟨λ m', ⟨λ n', _, omitted, omitted⟩, omitted, omitted⟩,
  exact tmul R (m * m') (n * n')
end

/-- The ring structure on the tensor product of two R-algebras -/
instance : ring (M ⊗[R] N) :=
{ mul := λ x y, tensor_product.mul.to_fun x y,
  mul_assoc := omitted,
  one := tmul R 1 1,
  one_mul := omitted,
  mul_one := omitted,
  left_distrib := omitted,
  right_distrib := omitted,
  ..tensor_product.add_comm_group M N }

lemma mul_def (m m' : M) (n n' : N) : tmul R m n * tmul R m' n' = tmul R (m * m') (n * n') := rfl

instance : comm_ring (A ⊗[R] B) :=
{ mul_comm := omitted,
  ..tensor_product.ring }

/-- The algebra structure on the tensor product of two R-algebras -/
instance : algebra R (M ⊗[R] N) := algebra.of_module omitted

@[simp] lemma algebra_map_tensor (r : R) : algebra_map (M ⊗[R] N) r = r • 1 := rfl

def tensor_inl : M →ₐ[R] M ⊗[R] N :=
{ to_fun := λ m, tmul R m 1,
  hom := ⟨rfl, by { intros, rw [mul_def, one_mul] }, λ x y, add_tmul x y 1⟩,
  commutes' := λ r, omitted }

def tensor_inr : N →ₐ[R] M ⊗[R] N :=
{ to_fun := λ n, tmul R 1 n,
  hom := omitted,
  commutes' := omitted }

def tensor_lift (f : A →ₐ[R] X) (g : B →ₐ[R] X) : A ⊗[R] B →ₐ[R] X :=
begin
  refine ⟨lift_aux _, _⟩,
  fapply linear_map.mk₂,
  exact (λ a b, f a * g b),
  all_goals {exact omitted}
end

def tensor_lift_equiv : ((A →ₐ[R] X) × (B →ₐ[R] X)) ≃ (A ⊗[R] B →ₐ[R] X) :=
⟨λ fg, tensor_lift fg.1 fg.2, λ f, ⟨f.comp tensor_inl, f.comp tensor_inr⟩, omitted, omitted⟩

end tensor_product

namespace quotient

def smul {I : ideal A} (r : R) : I.quotient → I.quotient :=
ideal.quotient.map _ _ (λ(x : A), r • x) (λ x h', by rw [smul_def]; exact I.mul_mem_left h')

@[simp] lemma smul_mk {I : ideal A} (r : R) (x : A) :
  quotient.smul r (ideal.quotient.mk I x) = ideal.quotient.mk I (r • x) :=
by refl

end quotient

instance quotient.algebra (I : ideal A) : algebra R I.quotient :=
{ smul := quotient.smul,
  smul_add := λ r x y, quotient.induction_on₂' x y $ λ a b, congr_arg (ideal.quotient.mk _) $
    smul_add r a b,
  add_smul := λ r s x, quotient.induction_on' x $ λ a, congr_arg (ideal.quotient.mk _) $
    add_smul r s a,
  mul_smul := λ r s x, quotient.induction_on' x $ λ a, congr_arg (ideal.quotient.mk _) $
    mul_smul r s a,
  one_smul := λ x, quotient.induction_on' x $ λ a, congr_arg (ideal.quotient.mk _) $
    by simp only [one_smul],
  zero_smul := λ x, quotient.induction_on' x $ λ a, congr_arg (ideal.quotient.mk _) $
    by simp only [zero_smul],
  smul_zero := λ r, congr_arg (ideal.quotient.mk _) $ by simp only [smul_zero],
  to_fun := ideal.quotient.mk I ∘ algebra_map A,
  commutes' := λ r x, quotient.induction_on' x $ λ a, congr_arg (ideal.quotient.mk _) $
    commutes r a,
  smul_def' := λ r x, quotient.induction_on' x $ λ a, congr_arg (ideal.quotient.mk _) $
    smul_def r a }

open mv_polynomial
local attribute [instance, priority 0] classical.prop_decidable
/-- An algebra `β` is finitely generated over a ring `α` if there is a finite subset `s` of `β` such that every element of `β` can be expressed as a polynomial in the elements of `s` with coefficients in `α` -/
def is_finitely_generated (α : Type u) [comm_ring α] (β : Type v) [comm_ring β] [algebra α β] :
  Prop :=
∃(s : finset β), ∀(x : β), ∃(p : mv_polynomial {x // x ∈ s} α),
  p.eval₂ (algebra_map β) subtype.val = x

def is_finitely_generated_base (α : Type u) [comm_ring α] : is_finitely_generated α α :=
⟨∅, λ x, ⟨C x, eval₂_C _ _ _⟩⟩

/-- Every quotient algebra is finitely generated -/
lemma is_finitely_generated_quotient {α : Type u} [comm_ring α] {β : Type v} [comm_ring β]
  [algebra α β] [decidable_eq α] [decidable_eq β] (h : is_finitely_generated α β) (I : ideal β) :
  is_finitely_generated α (I.quotient) :=
omitted

/-- The tensor product of two finitely generated algebras is finitely generated -/
lemma is_finitely_generated_tensor (hA : is_finitely_generated R A)
  (hB : is_finitely_generated R B) : is_finitely_generated R (A ⊗[R] B) :=
omitted

/-- The type of algebras over a fixed commutative ring. -/
structure Algebra (R : Type u) [comm_ring R] : Type max u (v+1) :=
  (β : Type v)
  (ring : ring β)
  (algebra : algebra R β)

attribute [instance] Algebra.ring Algebra.algebra
instance : has_coe_to_sort (Algebra.{u v} R) := { S := Type v, coe := Algebra.β }
-- instance Algebra.ring' (x : Algebra R) : ring x := by apply_instance
-- instance Algebra.algebra' (x : Algebra R) : algebra R x := by apply_instance

open category_theory
/-- The category of algebras over a fixed commutative ring. -/
instance Algebra.category : category (Algebra.{u v} R) :=
{ hom   := λ a b, a.β →ₐ[R] b.β,
  id    := λ a, alg_hom.id R a,
  comp  := λ a b c f g, alg_hom.comp g f }
