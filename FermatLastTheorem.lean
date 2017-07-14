-- A result in number theory conjectured by Pierre de Fermat and proven by Andrew Wiles and Richard Taylor.
-- Coloquially referred to as Fermat Last Theorem.
-- source: Modular Elliptic Curves and Fermat's Last Theorem, http://www.jstor.org/stable/2118559
-- source: Ring-Theoretic Properties of Certain Hecke Algebras, http://www.jstor.org/stable/2118560

axiom FABSorry : Π {A : Sort}, A

theorem FermatLastTheorem: ∀ (x y z n : nat), ((x > 0 ∧ y > 0 ∧ n > 2) → (x ^ n + y ^ n ≠ z ^ n)) :=
    FABSorry