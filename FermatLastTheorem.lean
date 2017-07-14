
structure meta_data : Type :=
mk_meta_data :: (authors : list string) (doi : list string) (results : list Sort) (description : string)

definition fermat_last_theorem := (∀ (x y z n : nat), ((x > 0 ∧ y > 0 ∧ n > 2) → (x ^ n + y ^ n ≠ z ^ n)))

definition fabstract : meta_data := {
    authors := ["Andrew Wiles", "Richard Tylor"],
    doi := ["10.2307/2118559", "10.2307/2118560"],
    results := [fermat_last_theorem],
    description := "A result in number theory conjectured by Pierre de Fermat and proven by Andrew Wiles and Richard Taylor. Coloquially referred to as Fermat Last Theorem."
    }