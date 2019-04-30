import ..basic category_theory.limits.limits


universes u u₁ u₂ v v₁ v₂

namespace category_theory
  open function
  variables {C : Type u₁} [𝒞 : category.{v₁} C]
  include 𝒞

  lemma injective_hom_op (X Y : C) : injective (@has_hom.hom.op _ _ X Y) :=
  λ f f' hf, by rw [←@has_hom.hom.unop_op _ _ _ _ f, ←@has_hom.hom.unop_op _ _ _ _ f', hf]

  lemma injective_hom_unop (X Y : Cᵒᵖ) : injective (@has_hom.hom.unop _ _ X Y) :=
  λ f f' hf, by rw [←@has_hom.hom.op_unop _ _ _ _ f, ←@has_hom.hom.op_unop _ _ _ _ f', hf]

end category_theory

open category_theory

namespace category_theory.nat_trans

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

protected def op {F F' : C ⥤ D} (η : F ⟹ F') : F'.op ⟹ F.op :=
{ app := λ x, (η.app $ unop x).op,
  naturality' := by { intros, simp, rw [←op_comp, ←op_comp, η.naturality] } }

protected def unop {F F' : Cᵒᵖ ⥤ Dᵒᵖ} (η : F ⟹ F') : F'.unop ⟹ F.unop :=
{ app := λ x, (η.app $ op x).unop,
  naturality' := by { intros, simp, rw [←unop_comp, ←unop_comp, η.naturality] } }

protected def unop' (F F' : C ⥤ D) (η : F.op ⟹ F'.op) : F' ⟹ F :=
{ app := λ x, (η.app $ op x).unop,
  naturality' :=
    by { intros, apply injective_hom_op, have := η.naturality f.op, simp at this, simp [this] } }

protected def op' (F F' : Cᵒᵖ ⥤ Dᵒᵖ) (η : F.unop ⟹ F'.unop) : F' ⟹ F :=
{ app := λ x, (η.app $ unop x).op,
  naturality' :=
    by { intros, apply injective_hom_unop, have := η.naturality f.unop, simp at this, simp [this] } }

end category_theory.nat_trans

open category_theory
namespace category_theory.nat_iso

variables {C : Type u₁} [𝒞 : category.{v₁} C] {D : Type u₂} [𝒟 : category.{v₂} D]
include 𝒞 𝒟

protected def op {F F' : C ⥤ D} (η : F ≅ F') : F'.op ≅ F.op :=
{ hom := nat_trans.op η.hom,
  inv := nat_trans.op η.inv,
  hom_inv_id' := omitted,
  inv_hom_id' := omitted }

protected def unop {F F' : Cᵒᵖ ⥤ Dᵒᵖ} (η : F ≅ F') : F'.unop ≅ F.unop :=
{ hom := nat_trans.unop η.hom,
  inv := nat_trans.unop η.inv,
  hom_inv_id' := omitted,
  inv_hom_id' := omitted }

protected def op_unop (F : C ⥤ D) : F.op.unop ≅ F :=
by { cases F, refl } -- maybe not the best definition

protected def unop_op (F : Cᵒᵖ ⥤ Dᵒᵖ) : F.unop.op ≅ F :=
by { cases F, refl } -- maybe not the best definition

protected def op_functor_const (d : D) :
  ((category_theory.functor.const C).obj d).op ≅ (category_theory.functor.const Cᵒᵖ).obj (op d) :=
by refl

end category_theory.nat_iso

open category_theory
namespace category_theory.limits

variables {J : Type v} [small_category J]
variables {C : Type u} [category.{v u} C]

protected def cocone.op {F : J ⥤ C} (s : cocone F) : cone F.op :=
⟨op s.X, s.ι.op⟩

protected def cone.op {F : J ⥤ C} (s : cone F) : cocone F.op :=
⟨op s.X, s.π.op⟩

protected def cocone.unop {F : Jᵒᵖ ⥤ Cᵒᵖ} (s : cocone F) : cone F.unop :=
⟨unop s.X, s.ι.unop⟩

protected def cone.unop {F : Jᵒᵖ ⥤ Cᵒᵖ} (s : cone F) : cocone F.unop :=
⟨unop s.X, s.π.unop⟩

protected def cocone.op' {F : Jᵒᵖ ⥤ Cᵒᵖ} (s : cocone F.unop) : cone F :=
⟨op s.X, s.ι.op' F ((category_theory.functor.const Jᵒᵖ).obj $ op s.X)⟩

protected def cone.op' {F : Jᵒᵖ ⥤ Cᵒᵖ} (s : cone F.unop) : cocone F :=
⟨op s.X, s.π.op' ((category_theory.functor.const Jᵒᵖ).obj $ op s.X) F⟩

protected def cocone.unop' {F : J ⥤ C} (s : cocone F.op) : cone F :=
⟨unop s.X, s.ι.unop' F ((category_theory.functor.const J).obj $ unop s.X)⟩

protected def cone.unop' {F : J ⥤ C} (s : cone F.op) : cocone F :=
⟨unop s.X, s.π.unop' ((category_theory.functor.const J).obj $ unop s.X) F⟩

def has_limit_op {F : J ⥤ C} (H : has_colimit F) : has_limit F.op :=
{ cone := H.cocone.op,
  is_limit :=
  { lift := λ s, (H.is_colimit.desc s.unop').op,
    fac' := omitted,
    uniq' := omitted } }

def has_colimit_op {F : J ⥤ C} (H : has_limit F) : has_colimit F.op :=
{ cocone := H.cone.op,
  is_colimit :=
  { desc := λ s, (H.is_limit.lift s.unop').op,
    fac' := omitted,
    uniq' := omitted } }

-- def has_limit_op {F : J ⥤ C} (H : has_colimit F) : has_limit F.op :=
-- { cone := H.cocone.op,
--   is_limit :=
--   { lift := λ s, begin unfreezeI, cases F, exact (H.is_colimit.desc s.unop).op end,
--     fac' := omitted,
--     uniq' := omitted } }

-- def has_colimit_op {F : J ⥤ C} (H : has_limit F) : has_colimit F.op :=
-- { cocone := H.cone.op,
--   is_colimit :=
--   { desc := λ s, begin unfreezeI, cases F, exact (H.is_limit.lift s.unop).op end,
--     fac' := omitted,
--     uniq' := omitted } }

def has_limit_unop {F : Jᵒᵖ ⥤ Cᵒᵖ} (H : has_colimit F) : has_limit F.unop :=
{ cone := H.cocone.unop,
  is_limit :=
  { lift := λ s, (H.is_colimit.desc s.op').unop,
    fac' := omitted,
    uniq' := omitted } }

def has_colimit_unop {F : Jᵒᵖ ⥤ Cᵒᵖ} (H : has_limit F) : has_colimit F.unop :=
{ cocone := H.cone.unop,
  is_colimit :=
  { desc := λ s, (H.is_limit.lift s.op').unop,
    fac' := omitted,
    uniq' := omitted } }

def has_limit_op' {F : Jᵒᵖ ⥤ Cᵒᵖ} (H : has_colimit F.unop) : has_limit F :=
{ cone := H.cocone.op',
  is_limit :=
  { lift := λ s, (H.is_colimit.desc s.unop).op,
    fac' := omitted,
    uniq' := omitted } }

def has_colimit_op' {F : Jᵒᵖ ⥤ Cᵒᵖ} (H : has_limit F.unop) : has_colimit F :=
{ cocone := H.cone.op',
  is_colimit :=
  { desc := λ s, (H.is_limit.lift s.unop).op,
    fac' := omitted,
    uniq' := omitted } }

def has_limit_unop' {F : J ⥤ C} (H : has_colimit F.op) : has_limit F :=
{ cone := H.cocone.unop',
  is_limit :=
  { lift := λ s, (H.is_colimit.desc s.op).unop,
    fac' := omitted,
    uniq' := omitted } }

def has_colimit_unop' {F : J ⥤ C} (H : has_limit F.op) : has_colimit F :=
{ cocone := H.cone.unop',
  is_colimit :=
  { desc := λ s, (H.is_limit.lift s.op).unop,
    fac' := omitted,
    uniq' := omitted } }

def has_limits_of_shape_op (H : has_colimits_of_shape J C) : has_limits_of_shape Jᵒᵖ Cᵒᵖ :=
λ F, has_limit_op' (H _)

end category_theory.limits