import meta_data
       .pure_type_systems

namespace Roux_C_and_vanDoorn_F_PTSs
open pure_type_system sum

def paper : document :=
{ authors := [ {name := "Cody Roux"}, {name := "Floris van Doorn"} ],
  title := "The structural theory of pure type systems",
  doi := "10.1007/978-3-319-08918-8_25" }

-- noncomputable theory

/- We investigate combinations and extensions of Pure Type Systems
   and their normalization properties. -/

variables ⦃P Q : pure_type_system⦄

/- We define a morphism between PTSs -/
definition morphism (P Q : pure_type_system) : Type :=
Σ'(f : P.Sorts → Q.Sorts), (∀s₁ s₂, P.Axioms s₁ s₂ → Q.Axioms (f s₁) (f s₂)) ∧
  (∀s₁ s₂ s₃, P.Relations s₁ s₂ s₃ → Q.Relations (f s₁) (f s₂) (f s₃))

/- It is easy to see that the domain of a morphism is weakly normalizing if the codomain is -/
unfinished is_weakly_normalizing_domain :
(Π P Q (f : morphism P Q) (HQ : is_weakly_normalizing Q),  is_weakly_normalizing P) :=
{ description := "It is easy to see that the domain of a morphism is weakly normalizing if the codomain is",
  sources := [cite.Document paper] }

/- The direct sum of PTSs -/
definition direct_sum (P Q : pure_type_system) : pure_type_system :=
⟨P.Sorts ⊕ Q.Sorts,
  λs₁ s₂, match s₁, s₂ with
  | (inl s₁), (inl s₂) := P.Axioms s₁ s₂
  | (inr s₁), (inr s₂) := Q.Axioms s₁ s₂
  | _, _               := false
  end,
  λs₁ s₂ s₃, match s₁, s₂, s₃ with
  | (inl s₁), (inl s₂), (inl s₃) := P.Relations s₁ s₂ s₃
  | (inr s₁), (inr s₂), (inr s₃) := Q.Relations s₁ s₂ s₃
  | _, _, _                      := false
  end⟩

/- It is normalizing if the original ones were -/
unfinished is_weakly_normalizing_direct_sum  :
  (Π P Q(HP : is_weakly_normalizing P) (HQ : is_weakly_normalizing Q),
    is_weakly_normalizing (direct_sum P Q)) :=
{ description := "It is normalizing if the original ones were",
  sources := [cite.Document paper] }

/- The direct sum with quantification over sorts in P added. This can be interpreted as the
  Q-logic of P-terms -/
definition forall_PTS (P Q : pure_type_system) : pure_type_system :=
⟨P.Sorts ⊕ Q.Sorts,
  λs₁ s₂, match s₁, s₂ with
  | (inl s₁), (inl s₂) := P.Axioms s₁ s₂
  | (inr s₁), (inr s₂) := Q.Axioms s₁ s₂
  | _, _               := false
  end,
  λs₁ s₂ s₃, match s₁, s₂, s₃ with
  | (inl s₁), (inl s₂), (inl s₃) := P.Relations s₁ s₂ s₃
  | (inr s₁), (inr s₂), (inr s₃) := Q.Relations s₁ s₂ s₃
  | (inl s₁), (inr s₂), (inr s₃) := true
  | _, _, _                      := false
  end⟩

/- It is normalizing if the original ones were -/
unfinished is_weakly_normalizing_forall :
  (Π P Q (HP : is_weakly_normalizing P) (HQ : is_weakly_normalizing Q),
     is_weakly_normalizing (forall_PTS P Q)) :=
{ description := "It is normalizing if the original ones were",
  sources := [cite.Document paper] }

/- The predicative polymorphic extension of P -/
definition poly (P : pure_type_system) : pure_type_system :=
⟨P.Sorts ⊕ P.Sorts × P.Sorts,
  λs₁ s₂, match s₁, s₂ with
  | (inl s₁), (inl s₂) := P.Axioms s₁ s₂
  | _, _               := false
  end,
  λs₁ s₂ s₃, match s₁, s₂, s₃ with
  | (inl s₁), (inl s₂), (inl s₃)                   := P.Relations s₁ s₂ s₃
  | (inl s₁), (inl s₂), (inr (s₁', s₂'))           := s₁ = s₁' ∧ s₂ = s₂'
  | (inl s₁), (inr (s₁', s₂')), (inr (s₁'', s₂'')) := s₁ = s₁' ∧ s₁' = s₁'' ∧ s₂' = s₂''
  | _, _, _                                        := false
  end⟩

/- It is normalizing if the original ones was -/
unfinished is_weakly_normalizing_poly :
  (Π P (HP : is_weakly_normalizing P), is_weakly_normalizing (poly P)) :=
{ description := "It is normalizing if the original ones was",
  sources := [cite.Document paper] }

def fabstract : fabstract := {
  description := "We investigate possible extensions of arbitrary given Pure Type Systems with additional sorts and rules which preserve the normalization property.",
  contributors := [{name := "Floris van Doorn"}],
  sources := [cite.Document paper],
  results := [result.Proof is_weakly_normalizing_domain,
              result.Proof is_weakly_normalizing_direct_sum,
              result.Proof is_weakly_normalizing_forall,
              result.Proof is_weakly_normalizing_poly],
}

end Roux_C_and_vanDoorn_F_PTSs
