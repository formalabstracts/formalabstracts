import ..basic
       ring_theory.algebra
       linear_algebra.tensor_product

universes u v w
variables {R : Type*} [comm_ring R]
variables {M : Type*} {N : Type*} [ring M] [ring N]
variables [algebra R M] [algebra R N]

local notation M ` ⊗[`:100 R `] ` N:100 := tensor_product R M N

namespace algebra

def of_module {R : Type u} {A : Type v} [comm_ring R] [ring A] [m : module R A]
  (h : ∀(r : R) (x y : A), r • x * y = x * r • y) : algebra R A :=
{ to_fun := λ r, r • 1,
  hom := ⟨one_smul R 1, by { intros, rw [h, one_mul, mul_smul] }, λ x y, add_smul x y 1⟩,
  commutes' := by { intros, rw [h, one_mul, ←h, mul_one] },
  smul_def' := by { intros, rw [h, one_mul] },
  ..m }

end algebra
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

protected def mul : M ⊗[R] N →ₗ[R] M ⊗[R] N →ₗ[R] M ⊗[R] N :=
begin
  refine tensor_product.lift ⟨λ m, ⟨λ n, _, omitted, omitted⟩, omitted, omitted⟩,
  refine tensor_product.lift ⟨λ m', ⟨λ n', _, omitted, omitted⟩, omitted, omitted⟩,
  exact tmul R (m * m') (n * n')
end

protected def mul' : M ⊗[R] N → M ⊗[R] N → M ⊗[R] N :=
λ x y, tensor_product.mul.to_fun x y

instance : ring (M ⊗[R] N) :=
{ mul := tensor_product.mul',
  mul_assoc := omitted,
  one := tmul R 1 1,
  one_mul := omitted,
  mul_one := omitted,
  left_distrib := omitted,
  right_distrib := omitted,
  ..tensor_product.add_comm_group M N }

instance : algebra R (M ⊗[R] N) := algebra.of_module omitted

end tensor_product
