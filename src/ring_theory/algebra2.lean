import ..basic
       ring_theory.algebra
       linear_algebra.tensor_product
       ring_theory.ideal_operations
       category_theory.concrete_category
open set

universes u v w
variables {R : Type u} {S : Type*} [comm_ring R] [comm_ring S]
variables {M : Type*} {N : Type*} [ring M] [ring N]
variables [algebra R M] [algebra R N]

local notation M ` ⊗[`:100 R `] ` N:100 := tensor_product R M N

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

/-- The algebra structure on the tensor product of two R-algebras -/
instance : algebra R (M ⊗[R] N) := algebra.of_module omitted

end tensor_product

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
